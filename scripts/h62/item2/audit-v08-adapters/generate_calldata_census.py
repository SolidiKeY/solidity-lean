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


def render(template, modules=MODULES, marker=MARKER, *, stream=False, result_shapes=False):
    anchor = '  let constants := environment.constants.toList.mergeSort '
    if template.count(anchor) != 1:
        raise ValueError('Kernel collector anchor changed; review the generator')
    body = template[template.index(anchor):]
    if stream:
        sorted_line = '  let constants := environment.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)\n'
        if body.count(sorted_line) != 1:
            raise ValueError('Streaming collector sort changed; review the generator')
        body = body.replace(sorted_line, '  let constants := environment.constants.toList\n', 1)
    if result_shapes:
        shape_anchor = '    let axioms ← collectAxioms name\n'
        row_anchor = '    let row := Json.mkObj [("name", toJson name.toString),\n'
        if body.count(shape_anchor) != 1 or body.count(row_anchor) != 1:
            raise ValueError('Result-shape collector anchors changed; review the generator')
        shape = """    let resultShape ← liftTermElabM do
      forallTelescope info.type fun values result => do
        let headInfo := fun (expression : Expr) =>
          match expression.getAppFn.constName? with
          | none => Json.null
          | some head => Json.mkObj [("name", toJson head.toString),
              ("module", toJson ((environment.getModuleIdxFor? head).map fun i =>
                environment.header.moduleNames[i]!.toString))]
        let equality := result.isAppOfArity ``Eq 3
        let args := result.getAppArgs
        let reflexive := if equality then args[1]! == args[2]! else false
        pure <| Json.mkObj [("binder_count", toJson values.size),
          ("head", headInfo result), ("is_equality", toJson equality),
          ("syntactic_reflexivity", toJson reflexive),
          ("lhs", if equality then headInfo args[1]! else Json.null),
          ("rhs", if equality then headInfo args[2]! else Json.null)]
"""
        body = body.replace(shape_anchor, shape + shape_anchor, 1)
        body = body.replace(row_anchor, row_anchor + '      ("result_shape", resultShape),\n', 1)
    required = ('environment.getModuleIdxFor? name', 'targets.findSome?',
                'collectAxioms name', 'IO.println (marker ++ row.compress)')
    if any(token not in body for token in required):
        raise ValueError('Kernel collector shape changed; review the generator')
    targets = ',\n'.join('    (`' + module + ', ' + json.dumps(marker) + ')'
                         for module in modules)
    note = ('P8 collector fields/filter are retained; only the global enumeration sort is omitted.'
            if stream else 'Collector body is reused verbatim from P8StatementCensus.')
    if result_shapes:
        note = ('P8 collector fields/filter are retained with additional structural result fields.'
                + (' Global enumeration sort is omitted.' if stream else ''))
    return ('import Lean\n' + ''.join('import ' + module + '\n' for module in modules)
            + '\n/-! Guards omission of match-valued theorem types that remain unresolved\n'
              'by the lexical census. Kernel inventory only: no witness or statement-\n'
              'fidelity acceptance. ' + note + ' -/\n'
              'open Lean Elab Command Meta\n\nrun_cmd do\n  let environment ← getEnv\n'
              '  let targets : Array (Name × String) := #[\n' + targets + '\n  ]\n' + body)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--name', required=True)
    parser.add_argument('--expect-sha256')
    parser.add_argument('--result-shapes', action='store_true', help='Capture structural conclusion heads; no semantic acceptance')
    parser.add_argument('--stream', action='store_true', help='Skip global sort; preserve every selected row and field')
    args = parser.parse_args()
    if re.fullmatch(r'[A-Za-z][A-Za-z0-9_-]*', args.name) is None:
        raise ValueError('Output name must be a simple owned filename')
    repo = args.repo.resolve()
    root = (repo / OUTPUT_ROOT).resolve()
    if root != repo / OUTPUT_ROOT:
        raise ValueError('Output escapes the owned repository scope')
    template = (repo / TEMPLATE).read_text()
    output = root / (args.name + '.lean')
    generated = render(template, stream=args.stream, result_shapes=args.result_shapes)
    digest = hashlib.sha256(generated.encode()).hexdigest()
    if args.expect_sha256 is not None and digest != args.expect_sha256:
        raise ValueError('Generated diagnostic hash differs from the pinned packet')
    root.mkdir(parents=True, exist_ok=True)
    with output.open('x') as handle:
        handle.write(generated)
    print(json.dumps({'output': str(output), 'modules': MODULES,
                      'sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
                      'result_shapes': args.result_shapes,
                      'enumeration': 'stream' if args.stream else 'sorted',
                      'collector_template_sha256': hashlib.sha256(template.encode()).hexdigest(),
                      'status': 'GENERATED_DIAGNOSTIC_ONLY'}))


if __name__ == '__main__':
    main()
