#!/usr/bin/env python3
"""List all module-owned kernel and compiler-added names, without exclusions.
Types remain in the accepted Expr DAG snapshot; compiler-only names have no
kernel signature in ModuleData and remain explicit unresolved inventory rows.
"""
import argparse,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('census',type=Path);a=ap.parse_args()
modules=sorted(json.loads(a.census.read_text())['owned'])
print('import Lean')
for module in modules: print('import '+module)
print('''open Lean
namespace H62PublicInventory
def nameJson : Name → Json
  | .anonymous => toJson (["anonymous"] : List String)
  | .str parent value => Json.arr #[toJson "str",nameJson parent,toJson value]
  | .num parent value => Json.arr #[toJson "num",nameJson parent,toJson (toString value)]
end H62PublicInventory''')
print("""open Lean in
run_elab do
  let env ← getEnv
  let requested : Array String := #["""+','.join(json.dumps(m) for m in modules)+"""]
  for moduleName in requested do
    let some index := env.header.moduleNames.findIdx? (fun name => name.toString == moduleName)
      | throwError "missing module {moduleName}"
    let data := env.header.moduleData[index]!
    unless data.constNames == data.constants.map (·.name) do
      throwError "kernel name/data mismatch"
    for (category,names) in [("kernel",data.constNames),("compiler_extra",data.extraConstNames)] do
      for name in names do
        IO.println ("H62-API " ++ (Json.mkObj [
          ("module",toJson moduleName),("name",toJson name.toString),
          ("category",toJson category),("name_parts",H62PublicInventory.nameJson name),
          ("private",toJson (isPrivateName name)),
          ("internal",toJson name.isInternal)]).compress)
    IO.println ("H62-API-MODULE " ++ (Json.mkObj [
      ("module",toJson moduleName),("kernel",toJson data.constNames.size),
      ("compiler_extra",toJson data.extraConstNames.size)]).compress)
""")
