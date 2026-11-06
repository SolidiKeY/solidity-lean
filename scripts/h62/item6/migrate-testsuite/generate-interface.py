#!/usr/bin/env python3
"""Generate a read-only compiled declaration/type census, including private names.
Output is version-sensitive raw Expr representation, not a semantic equivalence proof.
No proof/resource options are raised. Bulk stdout belongs off git.
"""
import argparse,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('census',type=Path);a=ap.parse_args()
s=json.loads(a.census.read_text())
print('import Lean')
for m in sorted(s['owned']): print('import '+m)
print('''
open Lean in
run_elab do
  let env ← getEnv
  let entries := env.constants.fold (init := #[]) fun acc name info =>
    match env.getModuleIdxFor? name with
    | none => acc
    | some index =>
      let owner := env.header.moduleNames[index.toNat]!
      if owner.toString.startsWith "Solidity.TestSuite." then
        acc.push (name, owner, info)
      else acc
  unless entries.size > 0 do throwError "empty TestSuite interface census"
  for name in [``Solkey.TestSuite.additionStorageWrite.proved,
      ``Solkey.TestSuite.storageRootReadWrite.proved,
      ``Solkey.TestSuite.additionStorageWrite.problem] do
    unless entries.any (fun entry => entry.1 == name) do
      throwError "missing frozen representative {name}"
  let entries := entries.qsort (fun a b => a.1.toString < b.1.toString)
  for (name, owner, info) in entries do
    let kind := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let row := Json.mkObj [
      ("kind", toJson kind),
      ("name", toJson name.toString),
      ("module", toJson owner.toString),
      ("levels", toJson (info.levelParams.map Name.toString)),
      ("raw_type", toJson (reprStr info.type)),
      ("internal", toJson name.isInternal)]
    liftIO <| IO.println ("H62-INTERFACE " ++ row.compress)
''')

for module in sorted(s['owned']):
    print('open Lean in\nrun_elab do')
    print('  let env ← getEnv')
    print('  let moduleName := '+json.dumps(module))
    print('  unless env.header.moduleNames.any (fun name => name.toString == moduleName) do')
    print('    throwError "missing imported module {moduleName}"')
    print('  let count := env.constants.fold (init := 0) fun count name _ =>')
    print('    match env.getModuleIdxFor? name with')
    print('    | none => count')
    print('    | some index => if env.header.moduleNames[index.toNat]!.toString == moduleName then count + 1 else count')
    print('  liftIO <| IO.println ("H62-MODULE " ++ (Json.mkObj [("module",toJson moduleName),("count",toJson count)]).compress)')
