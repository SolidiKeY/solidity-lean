#!/usr/bin/env python3
"""Generate bounded Lean audit batches from the pinned Source candidate list."""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
modules = (ROOT / 'tests/h55/shared-fixtures/source-exec-modules.txt').read_text().splitlines()
if len(modules) != 74 or len(set(modules)) != len(modules):
    raise SystemExit('unexpected candidate module list')
if any(not re.fullmatch(r'Solidity\.Lowering\.V08\.[A-Za-z0-9_]+Controls', m) for m in modules):
    raise SystemExit('invalid module name')
out = pathlib.Path(sys.argv[1])
out.mkdir(parents=True, exist_ok=True)
for start in range(0, len(modules), 8):
    group = modules[start:start + 8]
    code = 'import Lean\n' + ''.join(f'import {m}\n' for m in group)
    code += '''
open Lean Elab Command
run_cmd do
  let env ← getEnv
'''
    code += '  let modules := #[' + ', '.join('`' + m for m in group) + ']\n'
    code += '''  for modName in modules do
    let some idx := env.getModuleIdx? modName
      | throwError "module is not imported: {modName}"
    let names := (env.constants.toList.filterMap fun (name, _) =>
      if env.getModuleIdxFor? name == some idx then some name else none).mergeSort Name.quickLt
    for name in names do
      let some info := env.find? name | throwError "missing declaration: {name}"
      let axioms ← collectAxioms name
      let row := Json.mkObj [("module", toJson modName.toString), ("name", toJson name.toString),
        ("typeExpr", toJson (reprStr info.type)), ("levelParams", toJson (info.levelParams.map Name.toString)),
        ("valueExpr", toJson (if info.isTheorem then none else (info.value? true).map reprStr)),
        ("axioms", toJson ((axioms.toList.mergeSort Name.quickLt).map Name.toString)),
        ("theorem", toJson info.isTheorem), ("unsafe", toJson info.isUnsafe),
        ("partial", toJson info.isPartial), ("axiom", toJson info.isAxiom)]
      IO.println ("H55_DECL " ++ row.compress)
'''
    (out / f'Batch{start // 8:02}.lean').write_text(code)
