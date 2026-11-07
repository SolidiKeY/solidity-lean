#!/usr/bin/env python3
"""Guard regression: diagnostics or rejected proposals silently count as proof passes."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'tests/automation/'
ROLES = {
    'ClosedSpecProposal': ('checked positive and pending negative closed specifications', 'ClosedSpecs.ast.json', 'writes .lake/closed-spec-results.json'),
    'ClosedSpecRejected': ('corrupted native proposal must be rejected and state recovered', 'ClosedSpecs.ast.json and deliberately corrupted plugin', 'writes rejected and healthy-after-rejection JSON; driver writes plugin and log artifacts'),
    'DerivationCertificate': ('diagnostic residue certificate; remaining leaves do not prove source specification', 'command invocation and its imported source', 'command writes requested output and logs diagnostics'),
    'DirectCheck': ('direct verdict controls; positive and false specifications have distinct expected results', 'ClosedSpecs.ast.json', 'writes .lake/direct-check-results.json'),
    'DirectRuntime': ('compact runtime admission checks; external verdicts are distinct from kernel proof', 'ClosedSpecs.ast.json and DirectRuntimeAdmission.ast.json', 'logs results'),
    'ImportedAudit': ('synthetic reused-name axiom audit checks confined to restored command states', 'imported declarations and Lean environment', 'uses a temporary directory and logs or throws during elaboration'),
    'ProfileSimp': ('native tactic profiling diagnostic, not a general proof', 'SimpPreparation.ast.json and profiling environment', 'writes .lake/profile-simp-result.json and stderr timing markers'),
    'ReplayCosts': ('replay split timing diagnostic, not full source correctness', 'generated case commands and imported source', 'command writes requested JSON and stderr timing markers'),
    'SimpPreparation': ('positive proofs and false pending controls with storage fallback', 'SimpPreparation.ast.json', 'writes .lake/simp-preparation-results.json'),
}
CI = {'ClosedSpecProposal', 'DirectRuntime', 'ImportedAudit', 'SimpPreparation'}


def classify(root, manifest):
    if not isinstance(manifest, dict) or not isinstance(manifest.get('rows'), list):
        raise ValueError('invalid census')
    root = Path(root).resolve()
    out, seen = [], set()
    for row in manifest['rows']:
        if not isinstance(row, dict) or not isinstance(row.get('path'), str):
            raise ValueError('invalid candidate')
        path = row['path']
        if not path.startswith(PREFIX):
            continue
        name = path[len(PREFIX):]
        if not name.endswith('.lean') or name[:-5] not in ROLES or path in seen:
            raise ValueError('unreviewed or duplicate candidate')
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError('invalid source')
        if hashlib.sha256(source.read_bytes()).hexdigest() != row.get('sha256'):
            raise ValueError('source differs from census')
        name = name[:-5]
        role, inputs, effects = ROLES[name]
        driver = ('.github/workflows/pages.yml; current applicability unverified' if name in CI else
                  'scripts/check-spec-proposal.py; current applicability unverified' if name == 'ClosedSpecRejected' else
                  'scripts/measure-replay-costs.py generates runner; current applicability unverified' if name == 'ReplayCosts' else
                  'unresolved current invocation')
        out.append({'candidate': row, 'role': role, 'driver': driver, 'inputs': inputs + '; current bytes unverified',
                    'effects': effects, 'expected_outcome': 'successful Lean exit and rejection/fallback markers required; current run unresolved' if name == 'ClosedSpecRejected' else 'unresolved for current invocation',
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: automation_controls.py CENSUS.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'unverified-subsets-accepted',
                          'census_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError) as exc:
        print(f'automation classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
