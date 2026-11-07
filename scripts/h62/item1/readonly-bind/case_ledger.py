#!/usr/bin/env python3
"""Guard dropped original readonly declarations and unverified fixture promotion.

Exact byte transformation accounting for three pinned files, with source-only
fixture references. This does not certify Lean elaboration, private kernel
identity restoration, witness coverage, owner authority or body equivalence.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
FROZEN_SHA = 'e07aa0fe5f1a94c292c6d9edc22eee478f45c560b1802fab5e7ac581da9a2ffb'
PREFIX = 'Solidity.Lowering.Readonly.'
HERE = Path(__file__).resolve().parent

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result

overlay = load('bind_overlay', HERE/'overlay.py')
census = load('bind_census', ROOT/'scripts/h62/item2/audit-readonly-calls/census.py')
DECL = re.compile(r'(?m)^(private )?(theorem|def) ([A-Za-z_][A-Za-z_0-9]*)\b')

# One semantic branch description and source reference per original public law.
CASES = {
 'CapturePhases.compose': ('all capture phases succeed and code admission holds', 'Solidity/Lowering/Readonly/FullCaptureControls.lean', 'Solidity.Lowering.Readonly.FullCaptureControls.capture_fact'),
 'CaptureFailures.target_failed': ('receiver evaluation fails', 'Solidity/Lowering/Readonly/CaptureFailureControls.lean', 'Solidity.Lowering.Readonly.CaptureFailureControls.receiver_exhaustion'),
 'CaptureFailures.value_failed': ('receiver succeeds then value evaluation fails', 'tests/h62/item1/readonly-bind/PhaseControls.lean', 'Solidity.H62.ReadonlyBind.PhaseControls.value_timeout'),
 'CaptureFailures.arguments_failed': ('receiver/value succeed then arguments fail', 'tests/h62/item1/readonly-bind/PhaseControls.lean', 'Solidity.H62.ReadonlyBind.PhaseControls.arguments_timeout'),
 'CaptureFailures.encoding_failed': ('receiver/value/arguments succeed then encoding fails', 'tests/h62/item1/readonly-bind/EncodingFailureControls.lean', 'Solidity.H62.ReadonlyBind.EncodingFailureControls.encoding_failure'),
 'CaptureFailures.code_rejected': ('capture succeeds then code admission fails', 'Solidity/Lowering/Readonly/CaptureFailureControls.lean', 'Solidity.Lowering.Readonly.CaptureFailureControls.rejected_after_arguments'),
 'EnvironmentCredit.known': ('known instance and successful credit continue at final state', 'Solidity/Lowering/Readonly/EnvironmentCreditControls.lean', 'Solidity.Lowering.Readonly.EnvironmentCreditControls.static_credit_finishes'),
 'EnvironmentCredit.unknown': ('unknown instance skips credit and continues at recorded state', 'Solidity/Lowering/Readonly/EnvironmentCreditControls.lean', 'Solidity.Lowering.Readonly.EnvironmentCreditControls.unknown_credit_skipped'),
 'EnvironmentCredit.failed': ('known instance credit fails before continuation', 'Solidity/Lowering/Readonly/EnvironmentCreditControls.lean', 'Solidity.Lowering.Readonly.EnvironmentCreditControls.overflow_halts'),
 'EnvironmentCredit.callback_credit_failed': ('admitted callback credit fails before callback entry', 'Solidity/Lowering/Readonly/EnvironmentCreditControls.lean', 'Solidity.Lowering.Readonly.EnvironmentCreditControls.callback_overflow_halts'),
}


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def fixture(root, path, name):
    raw = (root/path).read_bytes()
    found = [r for r in census.declarations_text(path, raw.decode())
             if r['source_name'] == name and r['visibility'] == 'public']
    if len(found) != 1:
        raise ValueError('missing or duplicate scoped fixture theorem: '+name)
    return {'file': path, 'source_name': name, 'line': found[0]['line'],
            'source_sha256': digest(raw), 'status': 'source-reference-only-not-current-kernel-acceptance'}



def account(root, frozen, originals):
    if frozen['base'] != BASE or frozen['theorem_count'] != 792 or len(frozen['declarations']) != 792:
        raise ValueError('original792 membership drift')
    original_keys = [(r['file'], r['source_name']) for r in frozen['declarations']]
    if len(set(original_keys)) != 792:
        raise ValueError('duplicate original identity')
    original_by_key = dict(zip(original_keys, frozen['declarations']))
    rows = []
    files = []
    public = set()
    for module, expected_hash in overlay.HASHES.items():
        path = 'Solidity/Lowering/Readonly/'+module+'.lean'
        raw = originals[path]
        if digest(raw) != expected_hash:
            raise ValueError('frozen file hash drift: '+path)
        text = raw.decode()
        transformed, count = overlay.PATTERN.subn('', text, count=1)
        if count != 1:
            raise ValueError('original private helper ambiguity')
        transformed = 'import Solidity.Source.Hoare\n'+transformed
        transformed = re.sub(r'(?<![\w.])run_bind\b', 'Solidity.Source.Hoare.run_bind', transformed)
        current = (root/path).read_bytes()
        if current != transformed.encode():
            raise ValueError('exact statement-preserving migration drift: '+path)
        files.append({'file': path, 'original_sha256': digest(raw), 'current_sha256': digest(current)})
        declarations = list(DECL.finditer(census.mask(text)))
        if len(declarations) != {'CapturePhases': 5, 'CaptureFailures': 10, 'EnvironmentCredit': 10}[module]:
            raise ValueError('original declaration count drift')
        for match in declarations:
            name = PREFIX+module+'.'+match[3]
            row = {'file': path, 'source_name': name, 'line': text.count('\n',0,match.start())+1,
                   'kind': match[2], 'visibility': 'private' if match[1] else 'public'}
            if match[2] == 'theorem':
                original = original_by_key.get((path,name))
                if original is None or original['visibility'] != row['visibility']:
                    raise ValueError('original theorem absent or visibility drift')
                row['frozen_signature_sha256'] = original['signature_sha256']
                row['frozen_variable_context'] = original['variable_context']
            if match[3] == 'run_bind':
                row.update(status='removed-private-source-identity-unrestored',
                           replacement='Solidity.Source.Hoare.run_bind',
                           cases=[{'constructor': c, 'scope': 'synthetic bind only; no actual capture-phase witness inferred',
                                   'fixture': fixture(root, 'tests/h62/item1/readonly-bind/BindControls.lean',
                                       'Solidity.H62.ReadonlyBind.'+theorem)}
                                  for c, theorem in [('Except.ok','success_uses_returned_state'),
                                                     ('Except.error','error_keeps_returned_state')]])
            elif match[2] == 'theorem' and not match[1]:
                key = module+'.'+match[3]
                public.add(key)
                description, source, theorem = CASES[key]
                row.update(status='exact-source-statement-retained', cases=[{
                    'branch': description, 'fixture': fixture(root,source,theorem),
                    'scope': 'one source-level fixture; general premise feasibility and other gas/fork/halt/state cases not inferred'}])
            else:
                row.update(status='exact-source-declaration-retained',
                           cases=[{'branch': 'unchanged definition' if match[2]=='def' else 'unchanged helper equation',
                                   'status': 'source-fidelity-only'}])
            rows.append(row)
    if public != set(CASES) or len(rows) != 25 or len({(r['file'],r['source_name']) for r in rows}) != 25:
        raise ValueError('incomplete original declaration/case accounting')
    refs = [case['fixture'] for row in rows for case in row['cases'] if 'fixture' in case]
    return {'base': BASE, 'original792_count': 792, 'original_declaration_count': len(rows),
            'fixture_reference_records': len(refs),
            'distinct_fixture_source_identities': len({(r['file'],r['source_name']) for r in refs}),
            'counts': dict(Counter(r['status'] for r in rows)), 'files': files, 'rows': rows,
            'boundary': __doc__, 'full_goal_acceptance': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--frozen', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    raw = args.frozen.read_bytes()
    if digest(raw) != FROZEN_SHA:
        raise ValueError('frozen original792 artifact hash mismatch')
    originals = {f'Solidity/Lowering/Readonly/{m}.lean': subprocess.check_output(
        ['git','show',BASE+f':Solidity/Lowering/Readonly/{m}.lean'],cwd=ROOT) for m in overlay.HASHES}
    result = account(ROOT,json.loads(raw),originals)
    result['frozen_artifact_sha256'] = digest(raw)
    result['producer_sha256'] = digest(Path(__file__).read_bytes())
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('BIND_CASE_LEDGER_PASS original_declarations=25 public_cases=10 removed_private_identities=3; source-only')


if __name__ == '__main__':
    main()
