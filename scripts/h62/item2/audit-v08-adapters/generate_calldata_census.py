#!/usr/bin/env python3
"""Reuse the kernel collector for unresolved calldata theorem headers.

Generated diagnostics are off-Git materializations, not interface witnesses.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

MODULES = tuple('Solidity.Backend.CalldataPackets.' + name + '.Execution'
                for name in ('RawAddress', 'RawBool', 'RawInt', 'RawUintN'))
MARKER = 'H62_CALLDATA_CENSUS_JSON '
TEMPLATE = 'tests/h62/item2/audit-v08-adapters/P8StatementCensus.lean'
OUTPUT_ROOT = 'tests/h62/item2/audit-v08-adapters/generated-census'


def render(template, modules=MODULES, marker=MARKER):
    anchor = '  let constants := environment.constants.toList.mergeSort '
    if template.count(anchor) != 1:
        raise ValueError('Kernel collector anchor changed; review the generator')
    body = template[template.index(anchor):]
    required = ('environment.getModuleIdxFor? name', 'targets.findSome?',
                'collectAxioms name', 'IO.println (marker ++ row.compress)')
    if any(token not in body for token in required):
        raise ValueError('Kernel collector shape changed; review the generator')
    targets = ',\n'.join('    (`' + module + ', ' + json.dumps(marker) + ')'
                         for module in modules)
    return ('import Lean\n' + ''.join('import ' + module + '\n' for module in modules)
            + '\n/-! Guards omission of match-valued theorem types that remain unresolved\n'
              'by the lexical census. Kernel inventory only: no witness or statement-\n'
              'fidelity acceptance. Collector body is reused verbatim from P8StatementCensus. -/\n'
              'open Lean Elab Command Meta\n\nrun_cmd do\n  let environment ← getEnv\n'
              '  let targets : Array (Name × String) := #[\n' + targets + '\n  ]\n' + body)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--name', required=True)
    parser.add_argument('--expect-sha256')
    args = parser.parse_args()
    if re.fullmatch(r'[A-Za-z][A-Za-z0-9_-]*', args.name) is None:
        raise ValueError('Output name must be a simple owned filename')
    repo = args.repo.resolve()
    root = (repo / OUTPUT_ROOT).resolve()
    if root != repo / OUTPUT_ROOT:
        raise ValueError('Output escapes the owned repository scope')
    template = (repo / TEMPLATE).read_text()
    output = root / (args.name + '.lean')
    generated = render(template)
    digest = hashlib.sha256(generated.encode()).hexdigest()
    if args.expect_sha256 is not None and digest != args.expect_sha256:
        raise ValueError('Generated diagnostic hash differs from the pinned packet')
    root.mkdir(parents=True, exist_ok=True)
    with output.open('x') as handle:
        handle.write(generated)
    print(json.dumps({'output': str(output), 'modules': MODULES,
                      'sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
                      'collector_template_sha256': hashlib.sha256(template.encode()).hexdigest(),
                      'status': 'GENERATED_DIAGNOSTIC_ONLY'}))


if __name__ == '__main__':
    main()
