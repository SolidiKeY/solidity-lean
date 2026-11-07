"""Guard H90 residual parity accounting against lost rows and invented blockers.

Groups authenticated saved first-refusal observations only. Type occurrences are
context evidence, never causal diagnoses or proof of existing-route elaboration.
"""
from pathlib import Path
import argparse, collections, gzip, hashlib, json, subprocess
ROOT = Path(__file__).resolve().parents[3]
OWN = Path(__file__).resolve().parent
OUT = OWN / 'artifacts/h90'
HEAD = 'e0a5ac26ed521bde70e3ce4da5120d05a991d9ca'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def partition(rows):
    groups = collections.defaultdict(list)
    seen = set()
    for row in rows:
        key = tuple(row[k] for k in ('fixture', 'contract', 'function', 'sourceId'))
        require(type(row['sourceId']) is int and row['sourceId'] > 0, 'invalid function identity')
        require(key not in seen, 'duplicate function identity')
        seen.add(key)
        require(type(row['existingPrinted']) is bool and isinstance(row['canonical'], str)
                and bool(row['canonical']), 'invalid outcome')
        group = ('both' if row['canonical'] == 'ok' else 'printed-only') if row['existingPrinted'] else (
            'canonical-only' if row['canonical'] == 'ok' else 'neither')
        groups[group].append(row)
    return {k: groups[k] for k in ('both', 'printed-only', 'canonical-only', 'neither')}


def types_in(value, context='body'):
    result = collections.Counter()
    if isinstance(value, dict):
        if value.get('nodeType') == 'ElementaryTypeName':
            result[(context, value.get('name', '<missing>'))] += 1
        elif value.get('nodeType') == 'UserDefinedTypeName':
            result[(context, '<user-defined>')] += 1
        for key, child in value.items():
            result.update(types_in(child, key if value.get('nodeType') == 'FunctionDefinition' and key in ('parameters', 'returnParameters') else context))
    elif isinstance(value, list):
        for child in value:
            result.update(types_in(child, context))
    return result


def build():
    # Reuse the existing complete archive/source/row-identity verifier. No capture.
    subprocess.run(['python3', str(OWN / 'verify-h90-census.py')], cwd=ROOT, check=True)
    manifest = json.loads((OWN / 'h90-census-manifest.json').read_text())
    archive = manifest['archive']
    require(manifest['inputHead'] == HEAD, 'unauthorized input head')
    result = json.loads((OUT / 'cr-census-results.json').read_text())
    inputs = json.loads((OUT / 'cr-census-inputs.json').read_text())
    partitions = partition(result['rows'])
    functions = {}
    for fixture in inputs['fixtures']:
        document = json.loads((ROOT / fixture['copy']).read_text())
        todo = [(document, '')]
        while todo:
            value, contract = todo.pop()
            if isinstance(value, dict):
                if value.get('nodeType') == 'ContractDefinition':
                    contract = value.get('name', '')
                if value.get('nodeType') == 'FunctionDefinition':
                    key = (fixture['path'], contract, value.get('name', ''), value.get('id'))
                    require(key not in functions, 'duplicate AST function identity')
                    functions[key] = value
                todo.extend((v, contract) for v in value.values() if isinstance(v, (dict, list)))
            elif isinstance(value, list):
                todo.extend((v, contract) for v in value)
    for row in result['rows']:
        key = tuple(row[k] for k in ('fixture', 'contract', 'function', 'sourceId'))
        require(key in functions, 'census function missing from pinned AST')
    groups = collections.defaultdict(list)
    for row in partitions['printed-only']:
        key = tuple(row[k] for k in ('fixture', 'contract', 'function', 'sourceId'))
        require(key in functions, 'census function missing from pinned AST')
        node = functions[key]
        observed = types_in(node)
        groups[row['canonical']].append({
            'identity': dict(zip(('fixture', 'contract', 'function', 'sourceId'), key)),
            'functionAstSha256': digest(json.dumps(node, sort_keys=True, separators=(',', ':')).encode()),
            'typeOccurrences': [{'context': c, 'spelling': t, 'count': n}
                                for (c, t), n in sorted(observed.items())]})
    return {'guardedRegression': __doc__.splitlines()[0], 'inputHead': HEAD,
            'censusManifestSha256': digest((OWN / 'h90-census-manifest.json').read_bytes()),
            'sourceArchiveSha256': archive['sha256'], 'functions': len(result['rows']),
            'partitions': {k: len(v) for k, v in partitions.items()},
            'firstRefusals': [{'diagnostic': d, 'count': len(rows), 'functions': rows}
                              for d, rows in sorted(groups.items())],
            'boundary': 'Saved canonical first refusals for existing-printed functions only. Type occurrences do not identify the failing node or later blockers. Printed success is not elaboration, source transport, intrinsic closure or runtime correctness.'}


def controls():
    row = {'fixture': 'f', 'contract': 'C', 'function': 'f', 'sourceId': 1,
           'existingPrinted': True, 'canonical': 'ok'}
    rows = [dict(row, sourceId=i+1, existingPrinted=p, canonical=o)
            for i, (p, o) in enumerate([(True, 'ok'), (True, 'refusal'), (False, 'ok'), (False, 'refusal')])]
    require(all(len(v) == 1 for v in partition(rows).values()), 'partition control')
    for bad in [rows + [rows[0]], [dict(row, existingPrinted=1)], [dict(row, canonical='')],
                [dict(row, sourceId=True)]]:
        try:
            partition(bad)
        except ValueError:
            pass
        else:
            raise ValueError('malformed census accepted')
    shape = {'nodeType': 'FunctionDefinition', 'parameters': [{'nodeType': 'ElementaryTypeName', 'name': 'bytes'}],
             'returnParameters': [{'nodeType': 'UserDefinedTypeName'}],
             'body': {'nodeType': 'FunctionTypeName', 'parameters': [{'nodeType': 'ElementaryTypeName', 'name': 'uint8'}]}}
    require(types_in(shape) == collections.Counter({('parameters', 'bytes'): 1,
        ('returnParameters', '<user-defined>'): 1, ('body', 'uint8'): 1}), 'context control')
    print('PASS partition, duplicate/outcome/identity rejection and type-context controls')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--capture', action='store_true')
    parser.add_argument('--controls', action='store_true')
    args = parser.parse_args()
    if args.controls:
        controls()
        return
    report = build()
    raw = (json.dumps(report, indent=2) + '\n').encode()
    compressed = gzip.compress(raw, mtime=0)
    sha = digest(compressed)
    target = OUT / ('refusal-frontier-' + sha[:16] + '.json.gz')
    record = {'guardedRegression': report['guardedRegression'], 'inputHead': HEAD,
              'censusManifestSha256': report['censusManifestSha256'],
              'generatorSha256': digest(Path(__file__).read_bytes()),
              'partitions': report['partitions'], 'diagnostics': len(report['firstRefusals']),
              'archive': {'repositoryRelative': str(target.relative_to(ROOT)),
                          'sha256': sha, 'bytes': len(compressed)}, 'boundary': report['boundary']}
    pin = OWN / 'census-refusal-frontier-manifest.json'
    if args.capture:
        target.write_bytes(compressed)
        pin.write_text(json.dumps(record, indent=2) + '\n')
    else:
        require(json.loads(pin.read_text()) == record, 'frontier manifest drift')
        require(target.read_bytes() == compressed, 'frontier archive drift')
    print(json.dumps(record))


if __name__ == '__main__':
    main()
