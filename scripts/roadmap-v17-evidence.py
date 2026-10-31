#!/usr/bin/env python3
"""Read-only V17 evidence accounting. Successful accounting is never proof closure.

All inputs are untrusted claims. This checks their consistency and retained bytes;
it cannot authenticate a producer, interpret a Lean theorem, or discharge a premise.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import shutil
import sys

BASE = '2fe1f8932f96be15b00df03ba2cde46f64a87758'
LEDGER = 'docs/feature-work/roadmap-g03-ledger.json'
PIN_INPUTS = [LEDGER, 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
              'tests/migration/solkey.pin.json', 'tests/solkey/expected.tsv',
              'Solidity/TestSuite/Report.lean', 'scripts/evm-reference/generated.mjs',
              'scripts/evm-reference/replay.mjs', 'scripts/evm-reference/package-lock.json',
              'scripts/solidity-upstream.mjs', 'SolCases.lean', 'Solidity/Tools/SolCases.lean']
REQUIRED_GATES = ['runtime-keysort', 'clean-default', 'clean-compiler', 'clean-frontend',
                  'suite', 'corpus', 'axioms', 'trust', 'public-imports', 'artifacts',
                  'cache-equivalence', 'strict-correspondence', 'differential',
                  'layers', 'orphans', 'docs-no-new']
COMMANDS = {
    'runtime-keysort': ['lake', 'build', 'Solidity.KeySort'],
    'clean-default': ['lake', 'build'],
    'clean-compiler': ['lake', 'build', 'Solidity.Evm.Compiler'],
    'clean-frontend': ['lake', 'build', 'Solidity.Frontend.Import'],
    'suite': ['lake', 'build', 'SolkeyTestSuite'],
    'corpus': ['bash', 'scripts/check-corpus.sh'],
    'trust': ['bash', 'scripts/check-trust.sh'],
    'layers': ['node', 'scripts/check-layers.mjs'],
    'orphans': ['node', 'scripts/check-orphans.mjs'],
}
HEX = re.compile(r'[0-9a-f]{64}\Z')


def require(test, message):
    if not test:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def loads(data):
    def unique(pairs):
        out = {}
        for key, value in pairs:
            require(key not in out, 'duplicate JSON key: ' + key)
            out[key] = value
        return out
    return json.loads(data, object_pairs_hook=unique)


def load(path):
    return loads(Path(path).read_text())


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()


def snapshot(root):
    head = git(root, 'rev-parse', 'HEAD')
    subprocess.run(['git', '-C', str(root), 'merge-base', '--is-ancestor', BASE, head], check=True)
    require(not git(root, 'status', '--porcelain', '--untracked-files=all'), 'checkout is dirty')
    files = {p: digest((root / p).read_bytes()) for p in PIN_INPUTS}
    runtime = {}
    for name in ('lean', 'lake'):
        binary = shutil.which(name)
        require(binary is not None, 'tool missing from PATH: ' + name)
        runtime[name] = {'path': str(Path(binary).resolve()), 'sha256': digest(Path(binary).resolve().read_bytes()),
                         'version': subprocess.check_output([binary, '--version'], text=True, timeout=10).strip()}
    key = digest(json.dumps({'runtime': runtime, 'tree': git(root, 'rev-parse', 'HEAD^{tree}'),
                             'inputs': files}, sort_keys=True).encode())
    require(git(root, 'rev-parse', 'HEAD') == head and not git(root, 'status', '--porcelain', '--untracked-files=all'), 'checkout changed during snapshot')
    return {'schema': 1, 'revision': head, 'base': BASE, 'inputs': files,
            'repository': str(root.resolve()),
            'sourceTree': git(root, 'rev-parse', 'HEAD^{tree}'),
            'serialConfigSha256': digest((root / 'lakefile.toml').read_bytes().replace(
                b'weakLeanArgs = ["--tstack=131072"]', b'weakLeanArgs = ["--tstack=131072", "-j1"]')),
            'sourceToolchainKey': key, 'runtime': runtime, 'releaseClosed': False}


def local_file(root, name):
    require(isinstance(name, str) and name and not Path(name).is_absolute(), 'relative evidence path required')
    path = (root / name).resolve()
    require(path.is_relative_to(root.resolve()), 'evidence escapes root')
    require(path.is_file(), 'missing evidence: ' + name)
    return path


def aggregate(report, root, revision, required, current=None):
    require(report['schema'] == 1 and report['revision'] == revision, 'wrong schema/revision')
    require(report.get('unchangedCheckout', True) is True, 'checkout changed during gates')
    rows = {}
    for row in report['gates']:
        name = row['id']
        require(name not in rows, 'duplicate gate: ' + name)
        require(row['revision'] == revision, 'wrong gate revision: ' + name)
        require(isinstance(row['command'], list) and row['command'] and
                all(isinstance(x, str) and x for x in row['command']), 'missing command')
        if name in COMMANDS and row['status'] != 'pending':
            command = row['command']
            # Build probes may use the documented temporary serial config.
            if command[1:3] == ['-f', 'roadmap-v17-runtime.lakefile.toml']:
                command = command[:1] + command[3:]
            require(command == COMMANDS[name], 'mislabeled gate command: ' + name)
        require(type(row['exit']) is int or row['exit'] is None, 'invalid exit')
        require(row['status'] in ('pass', 'fail', 'pending'), 'unknown gate status')
        require((row['status'] == 'pass' and row['exit'] == 0) or
                (row['status'] == 'fail' and type(row['exit']) is int and row['exit'] != 0) or
                (row['status'] == 'pending' and row['exit'] is None), 'contradictory exit/status')
        require(HEX.fullmatch(row['sha256']) is not None, 'invalid checksum')
        data = local_file(root, row['log']).read_bytes()
        require(data and digest(data) == row['sha256'], 'empty/corrupt log: ' + name)
        if row['status'] != 'pending' and (name.startswith(('clean-', 'warm-')) or 'provenance' in row):
            require(current is not None, 'current source/toolchain snapshot required')
            require('provenance' in row and 'provenanceSha256' in row, 'missing build provenance')
            import importlib.util
            spec = importlib.util.spec_from_file_location('v17_provenance', Path(__file__).with_name('roadmap-v17-provenance.py'))
            provenance = importlib.util.module_from_spec(spec); spec.loader.exec_module(provenance)
            raw = provenance.read_bound(root, row['provenance'], row['provenanceSha256'])
            provenance.validate(loads(raw), root, current, name, row)
        if name == 'cache-equivalence' and row['status'] != 'pending':
            require(False, 'scoped pair preparation cannot discharge final cache-equivalence gate')
        rows[name] = row
    missing = sorted(set(required) - rows.keys())
    failed = sorted(k for k, v in rows.items() if v['status'] != 'pass')
    return {'schema': 1, 'revision': revision, 'missing': missing, 'failed': failed,
            'accountingComplete': not missing and not failed, 'releaseClosed': False}


def inventory(ledger):
    """Derive requirements from every actual ledger row; never a caller subset."""
    ids = ['child:' + x for x in ledger['workPackages']]
    ids += ['feature:' + x['id'] for x in ledger['features']]
    # Bind the entire row, including exclusions, observations, and stage owners.
    for field in ('combinations', 'symbolCombinations', 'decisions'):
        ids += [field + ':' + digest(json.dumps(x, sort_keys=True).encode()) for x in ledger[field]]
    require(len(ids) == len(set(ids)), 'duplicate inventory requirement')
    return sorted(ids)


def closure(report, ledger, revision, actual_imports):
    require(report['schema'] == 1 and report['revision'] == revision, 'wrong schema/revision')
    require(report['ledgerSha256'] == digest(json.dumps(ledger, sort_keys=True).encode()), 'wrong ledger')
    require(report['imports'] == actual_imports, 'public import inventory differs')
    expected = set(inventory(ledger))
    claims = {}
    theorems = {}
    for theorem in report['theorems']:
        name = theorem['name']
        require(name and name not in theorems, 'duplicate/empty theorem')
        require(theorem['module'] in actual_imports, 'theorem outside public imports')
        require(theorem['revision'] == revision, 'wrong theorem revision')
        require(theorem['kind'] in ('kernel', 'parameterized', 'external-test'), 'unknown proof kind')
        require(isinstance(theorem['axioms'], list) and
                set(theorem['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}, 'unapproved axiom')
        require(isinstance(theorem['premises'], list), 'missing premises')
        require(isinstance(theorem['observations'], list), 'missing observations')
        theorems[name] = theorem
    closed = set()
    # Acyclic premise accounting; a parameterized statement alone cannot close a row.
    for _ in theorems:
        for name, t in theorems.items():
            require(all(isinstance(p, str) and p in theorems for p in t['premises']), 'unmatched premise')
            if t['kind'] == 'kernel' and set(t['premises']) <= closed:
                closed.add(name)
    for row in report['claims']:
        name = row['id']
        require(name in expected and name not in claims, 'unknown/duplicate closure row: ' + name)
        require(row['status'] in ('done', 'partial', 'blocked', 'pending'), 'unknown closure status')
        require(row['revision'] == revision, 'wrong closure revision')
        if row['status'] == 'done':
            require(row['theorems'] and set(row['theorems']) <= closed, 'undischarged/parameterized-only claim')
            require(set(row['observations']) <= set().union(*(set(theorems[n]['observations']) for n in row['theorems'])),
                    'unmatched observation')
        claims[name] = row
    missing = sorted(expected - claims.keys())
    open_rows = sorted(k for k, v in claims.items() if v['status'] != 'done')
    return {'schema': 1, 'revision': revision, 'requiredRows': len(expected),
            'missing': missing, 'open': open_rows, 'unclosedTheorems': sorted(theorems.keys() - closed),
            'accountingComplete': not missing and not open_rows and set(theorems) == closed, 'releaseClosed': False,
            'boundary': 'Producer claims only; independent kernel/import/axiom gates and reviews still required.'}


def differential(report, root, revision):
    """Validate the published engine's retained matrix, without replacing it."""
    meta = report['metadata']
    require(meta['checkoutCommit'] == revision, 'historical differential revision')
    require(meta['gitDiffSha256'] == digest(b''), 'dirty differential producer')
    paths = {'runnerSha256': 'scripts/evm-reference/generated.mjs',
             'replaySha256': 'scripts/evm-reference/replay.mjs',
             'lockSha256': 'scripts/evm-reference/package-lock.json',
             'driverSha256': 'SolCases.lean', 'generatorSha256': 'Solidity/Tools/SolCases.lean',
             'generatorBinarySha256': '.lake/build/bin/solcases'}
    for field, path in paths.items():
        require(meta[field] == digest(local_file(root, path).read_bytes()), 'stale differential input: ' + path)
    pin = re.search(r"export const COMPILER_SHA = '([0-9a-f]{64})'", (root / 'scripts/solidity-upstream.mjs').read_text())
    require(pin and meta['compilerSha256'] == pin[1], 'wrong compiler pin')
    require(meta['enumerated'] == meta['selected'] == 160 and len(report['records']) == 160, 'partial enumeration')
    require(meta['compiler'] == '0.8.38+commit.1835d247.Emscripten.clang', 'wrong compiler version')
    counts = {'agree': 0, 'blocked': 0, 'mismatch': 0}
    kinds = set()
    for i, row in enumerate(report['records']):
        record = row['record']
        require(record['index'] == i and record['seed'] == meta['seed'], 'wrong index/seed')
        require(record['schema'] == 1 and type(record['kind']) is int and 0 <= record['kind'] < 10, 'invalid record schema/kind')
        kinds.add(record['kind'])
        seen = set()
        for actual in row['variants']:
            variant = actual['variant']
            require(type(variant['viaIR']) is bool and type(variant['optimizer']) is bool, 'invalid variant')
            key = (variant['viaIR'], variant['optimizer'])
            require(key not in seen, 'duplicate variant')
            seen.add(key)
            require(actual['index'] == i and actual['seed'] == meta['seed'], 'wrong variant identity')
            require(actual['sourceSha256'] == digest(record['source'].encode()), 'source mismatch')
            status = actual['status']
            require(status in counts, 'unknown differential status')
            counts[status] += 1
            if status == 'agree':
                for field in ('deployment', 'setup', 'before', 'run', 'storage', 'rawStorage', 'expected',
                              'creationCode', 'runtimeCode', 'creationSha256', 'runtimeSha256', 'layout'):
                    require(field in actual, 'missing retained observation: ' + field)
                require(actual['expected'] == record['expected'], 'changed expected verdict')
                for field in ('deployment', 'setup', 'before', 'run', 'storage', 'layout'):
                    require(isinstance(actual[field], dict), 'malformed retained observation: ' + field)
                require(isinstance(actual['rawStorage'], list), 'malformed raw storage')
                for code in ('creation', 'runtime'):
                    require(digest(bytes.fromhex(actual[code + 'Code'])) == actual[code + 'Sha256'], 'corrupt code')
                require(actual['deployment']['runtimeCodeSha256'] == actual['runtimeSha256'], 'deployment mismatch')
        require(seen == {(False, False), (False, True), (True, False), (True, True)}, 'incomplete settings matrix')
    require(kinds == set(range(10)), 'missing operation family')
    require(report['summary'] == counts, 'contradictory summary')
    published_differential(report, root)
    return {'schema': 1, 'revision': revision, 'summary': counts, 'kinds': sorted(kinds),
            'accountingComplete': counts['agree'] == 640, 'releaseClosed': False,
            'unsupported': ['callback combinations absent from published generated grammar'],
            'boundary': 'Retained bounded external evidence only; use published engine for comparisons.'}


def published_differential(report, root):
    """Use the reserved runner's own comparator and generator; no new oracle."""
    binary = root / '.lake/build/bin/solcases'
    raw = subprocess.check_output([str(binary), str(report['metadata']['seed'])], cwd=root, timeout=60)
    generated = [json.loads(line) for line in raw.splitlines()]
    require(generated == [r['record'] for r in report['records']], 'generated enumeration differs')
    check = subprocess.run(['node', str(root / 'scripts/roadmap-v17-compare.mjs')],
                           input=json.dumps(report).encode(), stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, cwd=root, timeout=60)
    require(check.returncode == 0 and check.stdout == b'V17_COMPARE_PASS\n',
            'published comparator failed: ' + check.stderr.decode(errors='replace')[:1000])


def verify_snapshot(report, current):
    require(report == current, 'revision/toolchain/input snapshot differs')
    return dict(current, accountingComplete=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['snapshot', 'aggregate', 'inventory', 'closure', 'differential', 'verify-snapshot'])
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--report', type=Path)
    parser.add_argument('--evidence-root', type=Path)
    args = parser.parse_args()
    snap = snapshot(args.root)
    mode = args.mode
    if mode == 'snapshot':
        result = snap
    elif mode == 'inventory':
        ledger = load(args.root / LEDGER)
        result = {'revision': snap['revision'], 'ledgerSha256': digest(json.dumps(ledger, sort_keys=True).encode()),
                  'requirements': inventory(ledger), 'releaseClosed': False}
    else:
        require(args.report is not None, '--report required')
        report = load(args.report)
        if mode == 'aggregate':
            require(args.evidence_root is not None, '--evidence-root required')
            result = aggregate(report, args.evidence_root, snap['revision'], REQUIRED_GATES, snap)
        elif mode == 'verify-snapshot':
            result = verify_snapshot(report, snap)
        elif mode == 'closure':
            imports = json.loads(subprocess.check_output(['node', str(args.root / 'scripts/roadmap-v17-imports.mjs')], cwd=args.root, timeout=60))
            result = closure(report, load(args.root / LEDGER), snap['revision'], imports['modules'])
        else:
            result = differential(report, args.root, snap['revision'])
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result.get('accountingComplete', mode in ('snapshot', 'inventory')) else 1


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        print(json.dumps({'error': str(error), 'releaseClosed': False}), file=sys.stderr)
        sys.exit(2)
