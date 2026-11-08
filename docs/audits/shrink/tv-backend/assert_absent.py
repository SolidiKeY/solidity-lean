#!/usr/bin/env python3
"""Check removed source theorem names against the rebuilt umbrella environment.
Usage: python3 .../assert_absent.py EXTERNAL_OUTPUT_DIRECTORY
This uses Lean, not a textual search. Run after the removal root rebuild.
"""
import json, pathlib, subprocess, sys
here = pathlib.Path(__file__).resolve().parent
out = pathlib.Path(sys.argv[1]).resolve(); out.mkdir(parents=True, exist_ok=True)
root = pathlib.Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
assert not out.is_relative_to(root)
rows = json.loads((here / "statements.json").read_text())
text = "import Solidity\nopen Lean Elab Command\n"
for group in rows.values():
    for row in group:
        name = json.dumps(row["name"], ensure_ascii=False)
        text += 'run_cmd do\n  if (← getEnv).contains (' + name + ').toName then throwError "removed theorem still present"\n'
text += 'run_cmd logInfo "REMOVED_EXPORTS_ABSENT_PASS"\n'
fixture = out / "Absent.lean"; fixture.write_text(text)
cmd = ["lake", "env", "lean", "-j1", "-M12288", "--tstack=131072", "--root=" + str(out), str(fixture)]
with (out / "absent.log").open("w") as log:
    result = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT)
print("REMOVED_EXPORTS_ABSENT", result.returncode); sys.exit(result.returncode)
