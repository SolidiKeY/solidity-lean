#!/usr/bin/env python3
"""Check removed theorem names and modules against the rebuilt umbrella.
Usage: python3 .../assert_absent.py EXTERNAL_OUTPUT_DIRECTORY
This queries the Lean environment, rather than searching source text.
"""
import json, os, pathlib, subprocess, sys
here = pathlib.Path(__file__).resolve().parent
out = pathlib.Path(sys.argv[1]).resolve(); out.mkdir(parents=True, exist_ok=True)
root = pathlib.Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
assert not out.is_relative_to(root)
rows = json.loads((here / "statements.json").read_text())
names = [row["name"] for group in rows.values() for row in group]
modules = json.loads((here / "family.json").read_text())
emitted = json.loads((here / "native-statements.json").read_text())
emitted_file = out / "emitted.txt"; emitted_file.write_text("\n".join(emitted) + "\n")
presence_file = out / "native-presence.json"
names_file = out / "names.txt"; names_file.write_text("\n".join(names) + "\n")
modules_file = out / "modules.txt"; modules_file.write_text("\n".join(modules) + "\n")
text = r'''import Solidity
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  for name in (← IO.FS.lines NAMES_FILE) do
    if env.contains name.toName then throwError "removed theorem still present: {name}"
  for name in (← IO.FS.lines MODULES_FILE) do
    if modules.contains name.toName then throwError "removed module still imported: {name}"
  let mut present : Array String := #[]
  let mut absent : Array String := #[]
  for name in (← IO.FS.lines EMITTED_FILE) do
    if env.contains name.toName then present := present.push name else absent := absent.push name
  let result := Json.mkObj [("present", toJson present), ("absent", toJson absent)]
  IO.FS.writeFile PRESENCE_FILE (result.pretty ++ "\n")
  logInfo "REMOVED_EXPORTS_AND_MODULES_ABSENT_PASS"
'''.replace("NAMES_FILE", json.dumps(str(names_file))).replace("MODULES_FILE", json.dumps(str(modules_file))).replace("EMITTED_FILE", json.dumps(str(emitted_file))).replace("PRESENCE_FILE", json.dumps(str(presence_file)))
fixture = out / "Absent.lean"; fixture.write_text(text)
cmd = ["lake", "env", "lean", "-j1", "-M12288", "--tstack=131072", "--root=" + str(out), str(fixture)]
with (out / "absent.log").open("w") as log:
    result = subprocess.run(cmd, env=dict(os.environ, LEAN_NUM_THREADS="1"), stdout=log, stderr=subprocess.STDOUT)
print("REMOVED_EXPORTS_AND_MODULES_ABSENT", len(names), len(modules), result.returncode)
sys.exit(result.returncode)
