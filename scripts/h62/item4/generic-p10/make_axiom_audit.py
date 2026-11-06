#!/usr/bin/env python3
"""Create local headline axiom guards; never edit central axiom pins."""
import argparse
import json
from pathlib import Path
import re
import census
from make_candidate import SOURCE

OUTPUT = Path('tests/h62/item4/generic-p10/GenericP10/AxiomAudit.lean')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def names(repo):
    controls = [r['name'] for r in census.declarations((repo/SOURCE).read_text(), str(SOURCE))
                if r['kind']=='theorem' and not r['private']]
    result = ['GenericP10.'+n for n in ['execute','ByteFixture','ByteCase','fixtureValues','fixture_word','fixture']]
    return result + [f'GenericP10.{namespace}.{n}' for namespace in ['ByteControls','Correspondence'] for n in controls]


def messages(report, expected):
    if report.get('success') is not True or report.get('partial') or report.get('timed_out') or report.get('failed_dependencies'):
        raise ValueError('incomplete or failed Lean diagnostic report')
    result = {}
    for item in report['items']:
        if item['severity'] != 'info': raise ValueError('unexpected non-info diagnostic')
        text = ' '.join(item['message'].split())
        match = re.fullmatch(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", text)
        if not match: raise ValueError(f'not an axiom report: {text}')
        name, axioms = match.groups()
        found = set(a.strip() for a in (axioms or '').split(',') if a.strip())
        if not found <= ALLOWED: raise ValueError(f'unapproved axioms for {name}: {found-ALLOWED}')
        if name in result: raise ValueError(f'duplicate axiom report: {name}')
        result[name] = text
    if set(result) != set(expected): raise ValueError('missing/extra headline axiom reports')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument('--diagnostics', type=Path, help='complete raw audit report; require fixed allowlist before pinning')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    expected = names(args.repo)
    reports = messages(json.loads(args.diagnostics.read_text()), expected) if args.diagnostics else None
    result = 'import GenericP10.Correspondence\n\n/-! Local headline guards; the core and central axiom inventories are unchanged. -/\n'
    for name in expected:
        if reports: result += f'/-- info: {reports[name]} -/\n#guard_msgs (whitespace := lax) in\n'
        result += f'#print axioms {name}\n'
    output = args.repo/OUTPUT
    if args.check:
        if output.read_text() != result: raise SystemExit('headline audit is not reproducible')
    else: output.write_text(result)
    print(f'AXIOM_AUDIT_SOURCE_PASS: {len(expected)} headlines; '+('allowlist validated and guards pinned' if reports else 'raw Lean report still required'))


if __name__ == '__main__': main()
