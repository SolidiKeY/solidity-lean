#!/usr/bin/env python3
"""Generate one module's kernel declaration/type census without forcing all env maps.
Including private declarations; compiler-only extraConstNames are not kernel declarations.
No budget override. Generate/run modules serially and validate the combined output.
"""
import argparse,json,re
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument("census",type=Path);ap.add_argument("--module",required=True);a=ap.parse_args()
s=json.loads(a.census.read_text())
if a.module not in s["owned"]: ap.error("module must be in assigned census")
record=s["owned"][a.module];expected=set()
for row in record["declaration_lines"]+record["commands"]:
    match=re.match(r"(?:theorem|lemma|def|abbrev|opaque|sol_auto_theorem) (Solkey\.TestSuite\.(?:[A-Za-z_][A-Za-z0-9_]*\.)*[A-Za-z_][A-Za-z0-9_]*)(?=\s|:|$)",row["text"])
    if match: expected.add(match[1])
if a.module=="Solidity.TestSuite.ScopedProblems": expected.add("Solkey.TestSuite.additionStorageWrite.problem")
print("import Lean\nimport "+a.module+"\nopen Lean in\nrun_elab do")
print("  let env ← getEnv\n  let moduleName := "+json.dumps(a.module))
print("""  let names := env.header.moduleNames
  let some index := names.findIdx? (fun name => name.toString == moduleName)
    | throwError "missing imported module {moduleName}"
  let data := env.header.moduleData[index]!
  unless data.constNames == data.constants.map (·.name) do
    throwError "module constant names/data disagree"
""")
for name in sorted(expected):
    print("  unless data.constNames.contains ``"+name+" do throwError "+json.dumps("missing frozen declaration "+name))
print("""  let entries := data.constants.qsort (fun a b => a.name.toString < b.name.toString)
  for info in entries do
    let name := info.name
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
      ("kind", toJson kind), ("name", toJson name.toString),
      ("module", toJson moduleName),
      ("levels", toJson (info.levelParams.map Name.toString)),
      ("raw_type", toJson (reprStr info.type)),
      ("internal", toJson name.isInternal)]
    IO.println ("H62-INTERFACE " ++ row.compress)
  IO.println ("H62-MODULE " ++ (Json.mkObj [("module",toJson moduleName),("count",toJson entries.size)]).compress)
""")
