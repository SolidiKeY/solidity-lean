#!/usr/bin/env python3
"""Check target coverage and fail-fast behavior without launching Lean.
The real cache/fixture gate is separate; mock output never proves a theorem.
"""
import json
import os
from pathlib import Path
import subprocess
import tempfile

repo = Path.cwd()
driver = repo / "tests/internal-flow/check-cached-files.sh"
owned = {str(p.with_suffix("")).replace("/", ".")
         for p in Path("Solidity/Backend/InternalFlow").glob("*.lean")}
fixtures = sorted(Path("tests/internal-flow").glob("*.lean"))
imports = set()
for fixture in fixtures:
    for line in fixture.read_text().splitlines():
        tokens = line.split("--", 1)[0].split()
        if tokens and tokens[0] == "import":
            imports.update(t for t in tokens[1:] if t.startswith("Solidity."))
assert owned and fixtures and imports
results = []
with tempfile.TemporaryDirectory(prefix="v12-cached-driver-") as tmp:
    root = Path(tmp)
    bindir = root / "bin"
    bindir.mkdir()
    lake = bindir / "lake"
    lake.write_text(r"""#!/usr/bin/env python3
import json, os, sys
with open(os.environ['V12_DRIVER_CALLS'], 'a') as log:
    log.write(json.dumps(sys.argv[1:]) + '\n')
mode = os.environ.get('V12_DRIVER_FAILURE', '')
if mode == 'build' and sys.argv[1] == 'build':
    sys.exit(61)
if mode == 'fixture' and sys.argv[1] == 'env':
    sys.exit(62)
""")
    lake.chmod(0o755)
    for mode, expected_exit in [("", 0), ("build", 61), ("fixture", 62)]:
        case = root / (mode or "success")
        case.mkdir()
        calls = case / "calls.jsonl"
        env = os.environ.copy()
        env.update(PATH=str(bindir) + os.pathsep + env.get("PATH", ""),
                   V12_DRIVER_CALLS=str(calls), V12_DRIVER_FAILURE=mode)
        outcome = subprocess.run(["bash", str(driver), str(case)], env=env,
                                 text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert outcome.returncode == expected_exit, outcome.stdout
        actual = [json.loads(line) for line in calls.read_text().splitlines()]
        assert actual[0][0] == "build" and set(actual[0][1:]) == owned | imports
        expected_fixtures = [["env", "lean", "-j1", "--tstack=131072", str(p)] for p in fixtures]
        if mode == "":
            assert actual[1:] == expected_fixtures
        elif mode == "build":
            assert len(actual) == 1
        else:
            assert actual[1:] == expected_fixtures[:1]
        results.append({"mode": mode or "success", "exit": outcome.returncode,
                        "recorded_calls": len(actual)})
print(json.dumps({"status": "pass", "owned_modules": len(owned),
                  "fixture_imports": len(imports), "fixtures": len(fixtures),
                  "controls": results}, indent=2))
