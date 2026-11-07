#!/usr/bin/env python3
"""Validate complete ModuleData name/type DAG streams, retaining unresolved extras.

This proves stream integrity, not semantic equivalence or complete export access.
Shared codec fingerprints preserve constructor data, binder names/order, universes
and canonical metadata without expanding shared expressions into enormous trees.
"""
import argparse
import collections
import hashlib
import json
import pathlib
import re
from census import BASE
from dag_support import codec, ROOT, INPUTS, OLD_VERSION, OLD_COMMIT, validate_scope, load

FAMILIES = ('noConfusion', 'recOn', 'casesOn', 'match_', 'toCtorIdx', '_proof_')
KINDS = {'axiom', 'definition', 'theorem', 'opaque', 'quotient', 'inductive', 'constructor', 'recursor'}


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True)


def digest(value):
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def name_flags(parts):
    private = False
    components = []
    while parts != ['anonymous']:
        if parts[0] == 'str':
            private |= parts == ['str', ['anonymous'], '_private']
            components.append(parts[2])
        parts = parts[1]
    return private, components


def has_level_mvar(value):
    return isinstance(value, list) and bool(value) and (value[0] == 'mvar' or any(has_level_mvar(v) for v in value))


def collect(scope, lines, lean_exit, source_commit=None):
    if type(lean_exit) is not int or lean_exit != 0:
        raise ValueError('INVENTORY_COMPILER_FAILED')
    if scope['base'] != BASE:
        raise ValueError('WRONG_BASE')
    expected = {row['module'] for row in scope['modules']}
    if len(expected) != len(scope['modules']) or not expected:
        raise ValueError('INVALID_SCOPE')
    dag = codec.DagStore(expected)
    needs, counts, entries, identities = {}, {}, {}, set()
    kernel_variants = collections.defaultdict(set)
    kernel_names, extra_names = set(), set()
    actual = {m: collections.Counter() for m in expected}
    header = complete = False
    for line in lines:
        prefix, _, payload = line.rstrip('\n').partition(' ')
        if prefix not in {'H62-NODE', 'H62-EXAMPLES-HEADER', 'H62-EXAMPLES-DECL', 'H62-EXAMPLES-EXTRA', 'H62-EXAMPLES-MODULE', 'H62-EXAMPLES-COMPLETE'}:
            if prefix.startswith('H62-EXAMPLES-'):
                raise ValueError('UNKNOWN_PROTOCOL_RECORD')
            continue
        if complete:
            raise ValueError('DATA_AFTER_COMPLETION')
        r = json.loads(payload)
        if prefix == 'H62-EXAMPLES-HEADER':
            if header or set(r) != {'schema', 'base', 'modules', 'lean_version', 'lean_commit', 'source_commit', 'capture_id'} or r['schema'] != 'h62-examples-dag-v1' or r['base'] != BASE:
                raise ValueError('INVALID_HEADER')
            if r['lean_version'] != OLD_VERSION or r['lean_commit'] != OLD_COMMIT:
                raise ValueError('WRONG_OLD_COMPILER')
            if not isinstance(r['source_commit'], str) or not re.fullmatch('[0-9a-f]{40}', r['source_commit']) or (source_commit is not None and r['source_commit'] != source_commit):
                raise ValueError('WRONG_SOURCE_COMMIT')
            if not isinstance(r['capture_id'], str) or not r['capture_id']:
                raise ValueError('INVALID_CAPTURE_ID')
            capture = {f: r[f] for f in ('lean_version', 'lean_commit', 'source_commit', 'capture_id')}
            if not isinstance(r['modules'], list) or len(r['modules']) != len(expected) or set(r['modules']) != expected:
                raise ValueError('INCOMPLETE_MODULE_HEADER')
            header = True
            continue
        if not header:
            raise ValueError('MISSING_HEADER')
        if prefix == 'H62-NODE':
            if r.get('tag') in ('fvar', 'mvar') or (r.get('tag') in ('sort', 'const') and has_level_mvar(r.get('data'))):
                raise ValueError('OPEN_DECLARATION_TYPE')
            dag.add(r)
            module = r['module']
            depth = needs.setdefault(module, [])
            children = [depth[i] for i in r['children']]
            tag = r['tag']
            if tag == 'bvar':
                required = int(r['data']) + 1
            elif tag in ('lam', 'forallE'):
                required = max(children[0], max(0, children[1] - 1))
            elif tag == 'letE':
                required = max(children[0], children[1], max(0, children[2] - 1))
            else:
                required = max(children, default=0)
            depth.append(required)
            continue
        if prefix in ('H62-EXAMPLES-DECL', 'H62-EXAMPLES-EXTRA'):
            category = 'kernel' if prefix == 'H62-EXAMPLES-DECL' else 'compiler_extra'
            required = {'module', 'name', 'name_parts', 'private_name'}
            required |= {'kind', 'unsafe', 'protected_name', 'level_parameters', 'type_root'} if category == 'kernel' else {'internal'}
            if not isinstance(r, dict) or set(r) != required or r['module'] not in expected or r['module'] in counts:
                raise ValueError('INVALID_DECLARATION_ROW')
            if not isinstance(r['name'], str) or not r['name'] or not codec.name_ok(r['name_parts']) or type(r['private_name']) is not bool:
                raise ValueError('INVALID_DECLARATION_NAME')
            private, parts = name_flags(r['name_parts'])
            if private != r['private_name']:
                raise ValueError('PRIVATE_NAME_FLAG_MISMATCH')
            name_key = canonical(r['name_parts'])
            identity = canonical([r['module'], category, r['name_parts']])
            if identity in identities:
                raise ValueError('DUPLICATE_DECLARATION_IDENTITY')
            identities.add(identity)
            if category == 'kernel':
                if r['kind'] not in KINDS or any(type(r[f]) is not bool for f in ('unsafe', 'protected_name')) or not isinstance(r['level_parameters'], list) or not all(codec.name_ok(n) for n in r['level_parameters']):
                    raise ValueError('INVALID_KERNEL_SIGNATURE')
                root = dag.root(r['module'], r['type_root'])
                if needs[r['module']][r['type_root']] != 0:
                    raise ValueError('OPEN_BOUND_VARIABLE')
                signature = {k: r[k] for k in ('kind', 'unsafe', 'level_parameters', 'private_name', 'protected_name')}
                signature['type_dag_sha256'] = root
                fingerprint = digest(signature)
                kernel_names.add(name_key)
                kernel_variants[name_key].add(fingerprint)
            else:
                if type(r['internal']) is not bool or r['internal'] != any(p.startswith('_') for p in parts):
                    raise ValueError('INVALID_EXTRA_NAME_FLAG')
                signature = fingerprint = None
                extra_names.add(name_key)
            entries[identity] = {'module': r['module'], 'name': r['name'], 'name_parts': r['name_parts'], 'category': category,
                                 'private_name': private, 'old_signature': signature, 'signature_sha256': fingerprint,
                                 'new_signature': None, 'shim_signature': None, 'shim_name': None,
                                 'export_visibility': 'unresolved', 'excluded': False,
                                 'generated_family_candidates': [f for f in FAMILIES if any(p.lstrip('_').startswith(f.lstrip('_')) for p in parts)]}
            actual[r['module']][category] += 1
            continue
        if prefix == 'H62-EXAMPLES-MODULE':
            if set(r) != {'module', 'kernel', 'compiler_extra', 'nodes'} or r['module'] not in expected or r['module'] in counts:
                raise ValueError('INVALID_MODULE_REPORT')
            if any(type(r[f]) is not int or r[f] < 0 for f in ('kernel', 'compiler_extra', 'nodes')):
                raise ValueError('INVALID_MODULE_COUNTS')
            dag.finish(r['module'])
            if dag.closed[r['module']] != r['nodes'] or any(actual[r['module']][f] != r[f] for f in ('kernel', 'compiler_extra')):
                raise ValueError('MODULE_COUNT_MISMATCH')
            needs.pop(r['module'], None)
            counts[r['module']] = r
            continue
        if set(r) != {'modules', 'kernel', 'compiler_extra'} or any(type(r[f]) is not int for f in r):
            raise ValueError('INVALID_COMPLETION')
        if set(counts) != expected or dag.hashes or r['modules'] != len(expected) or any(r[f] != sum(v[f] for v in counts.values()) for f in ('kernel', 'compiler_extra')):
            raise ValueError('INCOMPLETE_INVENTORY')
        complete = True
    if not complete or not any(v['kernel'] for v in counts.values()):
        raise ValueError('MISSING_OR_EMPTY_COMPLETION')
    # Existing generated declarations remain required; no family is excluded.
    sentinels = {'Solidity.Examples.SourceCounterexample': ['Solidity.Examples.SourceCounterexample.badRefuted'],
                 'Solidity.Examples.Tactics.Step': ['Solidity.Examples.Tactics.Step.reads', 'Solidity.Examples.Tactics.Step.writes']}
    names = {(v['module'], canonical(v['name_parts'])) for v in entries.values() if v['category'] == 'kernel'}
    for module, required in sentinels.items():
        for name in required if module in expected else []:
            parts = ['anonymous']
            for part in name.split('.'):
                parts = ['str', parts, part]
            if (module, canonical(parts)) not in names:
                raise ValueError('MISSING_GENERATED_SENTINEL')
    ordered = {key: entries[key] for key in sorted(entries)}
    summary = {'schema': 'h62-examples-dag-frozen-v1', 'base': BASE, 'status': 'old_inventory_recorded_new_parity_pending',
               'compiler': capture, 'modules': sorted(expected), 'module_counts': {key: counts[key] for key in sorted(counts)},
               'kernel_declarations': sum(v['kernel'] for v in counts.values()),
               'compiler_extra_names': sum(v['compiler_extra'] for v in counts.values()),
               'unique_kernel_names': len(kernel_names), 'unique_compiler_extra_names': len(extra_names),
               'unique_all_names': len(kernel_names | extra_names),
               'kernel_compiler_name_overlaps': len(kernel_names & extra_names),
               'module_data_kernel_reemissions': sum(v['kernel'] for v in counts.values()) - len(kernel_names),
               'kernel_names_with_multiple_signatures': {n:sorted(v) for n,v in sorted(kernel_variants.items()) if len(v)>1},
               'exclusions': 0, 'implemented_shims': [], 'entries_sha256': digest(ordered),
               'kernel_interface_sha256': digest({key: v['signature_sha256'] for key, v in ordered.items() if v['category'] == 'kernel'}),
               'boundary': 'Complete ModuleData occurrences, not exclusive source ownership: kernel names can be reemitted across modules and compiler tables can overlap kernel tables. All occurrences retained; extra signatures and export accessibility unresolved. Exact types require referenced structural DAG stream. No new parity, semantic equivalence, axiom equality or full H78 acceptance.'}
    return ordered, summary


def verify_provenance(scope, census_sha256, fixture, compiler, log_path):
    if fixture.get('toolchain_version') != OLD_VERSION:
        raise ValueError('WRONG_OLD_TOOLCHAIN_MANIFEST')
    if fixture.get('base') != BASE or fixture.get('original_scope_modules') != len(scope['modules']) or fixture.get('modules') != sorted(r['module'] for r in scope['modules']) or fixture.get('census_sha256') != census_sha256 or fixture.get('pinned_closure_equal') is not True:
        raise ValueError('UNVERIFIED_FROZEN_CENSUS')
    if not isinstance(fixture.get('source_commit'), str) or not re.fullmatch('[0-9a-f]{40}', fixture['source_commit']):
        raise ValueError('UNVERIFIED_SOURCE_COMMIT')
    inputs = fixture.get('inputs')
    if not isinstance(inputs, list) or len(inputs) != len(INPUTS) or {r.get('repository_path') for r in inputs} != set(INPUTS):
        raise ValueError('UNVERIFIED_CODEC_INPUTS')
    for row in inputs:
        if row.get('sha256') != hashlib.sha256((ROOT/row['repository_path']).read_bytes()).hexdigest():
            raise ValueError('CODEC_INPUT_CHANGED')
    command = compiler.get('command')
    if not isinstance(command, list) or len(command) != 6 or command[:5] != ['lake','env','lean','-j1','--tstack=131072'] or not isinstance(command[-1], str):
        raise ValueError('UNVERIFIED_COMPILER_COMMAND')
    if type(compiler.get('exit')) is not int or compiler['exit'] != 0 or 'stop' not in compiler or compiler['stop'] is not None or compiler.get('resource_violations') != []:
        raise ValueError('UNVERIFIED_COMPILER_RESULT')
    source = pathlib.Path(command[-1])
    generator = load('scripts/h62/item6/migrate-examples/generate-dag-inventory.py')
    expected = generator.generate(fixture['modules'], fixture['source_commit'], capture_id=fixture['capture_id'])
    if hashlib.sha256(expected.encode()).hexdigest() != fixture.get('fixture_sha256'):
        raise ValueError('FIXTURE_NOT_GENERATED_FROM_VERIFIED_INPUTS')
    if source.name != fixture.get('fixture_file') or hashlib.sha256(source.read_bytes()).hexdigest() != fixture.get('fixture_sha256'):
        raise ValueError('FIXTURE_CHANGED')
    if log_path.name != fixture.get('stream_file'):
        raise ValueError('WRONG_STREAM_FILE')
    return source

def verify_seal(lines, summary, fixture):
    records = [json.loads(line[len('H62-EXAMPLES-SEAL '):]) for line in lines if line.startswith('H62-EXAMPLES-SEAL ')]
    expected = dict(summary['compiler'])
    expected.update(stream_file=fixture['stream_file'], modules=len(summary['modules']),
                    kernel=summary['kernel_declarations'], compiler_extra=summary['compiler_extra_names'])
    if records != [expected] or summary['compiler']['capture_id'] != fixture['capture_id']:
        raise ValueError('COMPILER_STREAM_SEAL_MISMATCH')

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--census', type=pathlib.Path, required=True)
    p.add_argument('--log', type=pathlib.Path, required=True)
    p.add_argument('--compiler-result', type=pathlib.Path, required=True)
    p.add_argument('--fixture-manifest', type=pathlib.Path, required=True)
    p.add_argument('--output', type=pathlib.Path, required=True)
    a = p.parse_args()
    compiler = json.loads(a.compiler_result.read_text())
    fixture = json.loads(a.fixture_manifest.read_text())
    scope = json.loads(a.census.read_text())
    validate_scope(scope)
    compiler_log = a.compiler_result.with_suffix('.log')
    if not compiler_log.is_file():
        raise ValueError('MISSING_COMPILER_LOG')
    census_sha256 = hashlib.sha256(a.census.read_bytes()).hexdigest()
    verify_provenance(scope, census_sha256, fixture, compiler, a.log)
    from dependencies import Tree
    captured = Tree(ROOT, fixture['source_commit'])
    base = Tree(ROOT, BASE)
    if any(captured.blobs.get(r['path']) != base.blobs[r['path']] for r in scope['modules']):
        raise ValueError('CAPTURE_SOURCE_DIFFERS_FROM_FROZEN_EXAMPLES')
    with a.log.open() as stream:
        entries, summary = collect(scope, stream, 0, fixture['source_commit'])
    with compiler_log.open() as stream:
        verify_seal(stream, summary, fixture)
    a.output.mkdir(exist_ok=False)
    with (a.output/'inventory.jsonl').open('w') as output:
        for row in entries.values():
            output.write(canonical(row) + '\n')
    summary['raw_stream_file'] = a.log.name
    with a.log.open('rb') as stream:
        summary['raw_stream_sha256'] = hashlib.file_digest(stream, 'sha256').hexdigest()
    with compiler_log.open('rb') as stream:
        summary['compiler_log_sha256'] = hashlib.file_digest(stream,'sha256').hexdigest()
    summary['fixture_sha256'] = fixture['fixture_sha256']
    summary['census_sha256'] = census_sha256
    summary['compiler_result_sha256'] = hashlib.sha256(a.compiler_result.read_bytes()).hexdigest()
    summary['fixture_manifest_sha256'] = hashlib.sha256(a.fixture_manifest.read_bytes()).hexdigest()
    summary['verified_inputs'] = fixture['inputs']
    (a.output/'summary.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'module_counts' and k != 'modules'}))


if __name__ == '__main__':
    main()
