#!/usr/bin/env python3
"""Stage the H70 all-30 catalog transition through the generator adapter.

The adapter is `generator-adapter.patch` against scripts/solidity-feature-audit.py
(owned by the generator owner, not edited here). This driver runs the patched
generator in memory, with the real script path as `__file__`, so it reads the
real ledger and decision records and writes nothing outside --stage:

1. identity: on the active manifest the patched generator's --check passes, so
   applying the patch alone changes no generated file;
2. staging: the manifest with the 30 proposed rows (all30-proposal.json), each
   carrying `diagnostic: unsupported` and its H37/H70 withdrawal provenance,
   validates and renders Features.lean, FeatureInfo.lean and the report into
   --stage, plus Check.lean (both Lean files in one module) for a kernel check;
3. impact: lists the withdrawn features `ScopeScan.certify` would admit,
   because it tests scope before `Feature.unmodelled?`. Activation waits for the
   Source owner (VY5) to reject on `unmodelled?` first.

Staged outputs are evidence, not activatable: with the patch alone the
generated `WithinProfile`/`Feature.inProfile` still test scope only, so the
staged `Features.lean` lists the 30 withdrawn features in `outsideScope` and
admits them through `ProfileSyntax` as well as `ScopeScan.certify`.

Usage: adapter.py [--stage DIR]   (default: no staging, identity check only)
"""
import argparse, contextlib, copy, hashlib, io, json, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SCRIPT = ROOT / 'scripts/solidity-feature-audit.py'
PATCH = HERE / 'generator-adapter.patch'
RECORD = 'docs/feature-work/fullscope-vx1.md#h70-all-30-staged-manifest-and-generator-inventory'
WITHDRAWN_ON = '2026-11-06'


def patched_source():
    original = SCRIPT.read_text()
    with_patch = subprocess.run(['patch', '-s', '-o', '-', str(SCRIPT), str(PATCH)],
                                capture_output=True, text=True, check=True).stdout
    assert with_patch != original
    return with_patch


def run_generator(source, argv):
    namespace = {'__name__': '__main__', '__file__': str(SCRIPT)}
    old = sys.argv
    sys.argv = [str(SCRIPT), *argv]
    out = io.StringIO()
    try:
        with contextlib.redirect_stdout(out):
            exec(compile(source, str(SCRIPT), 'exec'), namespace)
    finally:
        sys.argv = old
    return out.getvalue()


def generator_module(source):
    namespace = {'__name__': 'feature_audit_adapter', '__file__': str(SCRIPT)}
    exec(compile(source, str(SCRIPT), 'exec'), namespace)
    return namespace


def mutation_controls(source, staged):
    """Each mutation of a withdrawn row must fail the patched validator."""
    gen = generator_module(source)
    ledger = json.loads((ROOT / 'docs/solidity-upstream-inventory.json').read_text())
    gen['validate'](staged, ledger)
    index = next(i for i, f in enumerate(staged['features']) if 'withdrawal' in f)
    prior = staged['features'][index]['withdrawal']['prior']
    mutations = {
        'active decision kept': lambda f: f.__setitem__('decision', prior),
        'diagnostic without withdrawal': lambda f: f.pop('withdrawal'),
        'withdrawal without diagnostic': lambda f: f.pop('diagnostic'),
        'claimed present': lambda f: f.__setitem__('current', 'present'),
        'kept excluded': lambda f: (f.__setitem__('scope', 'exclude'), f.__setitem__('current', 'notApplicable')),
        'wrong prior outcome': lambda f: f['withdrawal'].__setitem__('prior', dict(prior, outcome='approved')),
        'missing record': lambda f: f['withdrawal'].__setitem__('record', 'docs/nowhere.md#h70'),
        'missing anchor': lambda f: f['withdrawal'].__setitem__('record', RECORD.split('#')[0] + '#no-such-heading'),
    }
    for name, mutate in mutations.items():
        mutant = copy.deepcopy(staged)
        mutate(mutant['features'][index])
        try:
            gen['validate'](mutant, ledger)
        except (AssertionError, KeyError):
            continue
        raise SystemExit(f'mutation accepted: {name}')
    return len(mutations)


def staged_manifest():
    proposal = json.loads((HERE / 'all30-proposal.json').read_text())
    manifest = json.loads((ROOT / 'docs/solidity-features.json').read_text())
    assert hashlib.sha256((ROOT / 'docs/solidity-features.json').read_bytes()).hexdigest() == \
        proposal['manifestSha256'], 'active manifest moved since the proposal'
    rows = {row['id']: row for row in proposal['rows']}
    staged = copy.deepcopy(manifest)
    for i, feature in enumerate(staged['features']):
        if feature['id'] in rows:
            row = rows[feature['id']]
            assert feature == row['before']
            new = dict(row['proposed'])
            new['diagnostic'] = 'unsupported'
            new['withdrawal'] = {'question': 'H37/H70', 'date': WITHDRAWN_ON, 'record': RECORD,
                                 'prior': row['before']['decision']}
            staged['features'][i] = new
    assert sum('withdrawal' in f for f in staged['features']) == 30
    return staged


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument('--stage', type=Path)
    args = p.parse_args()
    source = patched_source()
    print('identity:', run_generator(source, ['--check']).strip().replace('\n', '; '))
    staged = staged_manifest()
    print(f'mutations: {mutation_controls(source, staged)} withdrawn-row mutations rejected')
    admitted = [f['id'] for f in staged['features']
                if f.get('diagnostic') == 'unsupported' and f['scope'] in ('model', 'abstract')]
    print(f'impact: {len(admitted)} withdrawn features pass the scope test of ScopeScan.certify '
          'and need its unmodelled? test first (VY5):', ', '.join(admitted))
    if __debug__ is False:
        raise SystemExit('run without -O: validation and --check are assertions')
    if args.stage:
        args.stage.mkdir(parents=True, exist_ok=True)
        manifest = args.stage / 'solidity-features.json'
        manifest.write_text(json.dumps(staged, indent=2, ensure_ascii=False) + '\n')
        print('staged:', run_generator(source, ['--manifest', str(manifest), '--out-dir', str(args.stage)])
              .strip().replace('\n', '; '))
        features = (args.stage / 'Features.lean').read_text()
        info = (args.stage / 'FeatureInfo.lean').read_text()
        assert info.startswith('import Solidity.Language.Features\n')
        (args.stage / 'Check.lean').write_text(
            features + '\n' + info.removeprefix('import Solidity.Language.Features\n'))
        sums = [f"{hashlib.sha256((args.stage / n).read_bytes()).hexdigest()}  {n}"
                for n in ['solidity-features.json', 'Features.lean', 'FeatureInfo.lean',
                          'solidity-feature-inventory.md', 'Check.lean']]
        (args.stage / 'SHA256SUMS').write_text('\n'.join(sums) + '\n')
        print('\n'.join(sums))


if __name__ == '__main__':
    main()
