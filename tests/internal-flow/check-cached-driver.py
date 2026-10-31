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
registry = json.loads(Path("tests/internal-flow/fixture-axiom-pins.json").read_text())
assert set(registry) == {p.stem for p in fixtures}, "fixture registry coverage"
for entry in registry.values():
    source = Path(entry["guard"]).read_text()
    scope = {}
    # Existing owned guards define literal PINS plus explicit updates before IO.
    exec(source[source.index("PINS = "):source.index("log = Path(sys.argv[1])")], {}, scope)
    assert entry["pins"] == scope["PINS"], "registry differs from existing exact guard"

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
    node = bindir / "node"
    node.write_text(r'''#!/usr/bin/env python3
import json, os, sys
with open(os.environ["V12_DRIVER_CALLS"], "a") as log:
    log.write(json.dumps(["node", *sys.argv[1:]]) + "\n")
if os.environ.get("V12_DRIVER_FAILURE") == "fixture:" + sys.argv[3]:
    sys.exit(62)
''')
    node.chmod(0o755)
    for mode, expected_exit in [("", 0), ("build", 61), *[("fixture:" + str(p), 62) for p in fixtures]]:
        case = root / (mode.replace("/", "_").replace(":", "_") or "success")
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
        expected_fixtures = [["node", "tests/internal-flow/fixture-cache.mjs", "check", str(p), str(case)] for p in fixtures]
        if mode == "":
            assert actual[1:] == expected_fixtures
        elif mode == "build":
            assert len(actual) == 1
        else:
            index = next(i for i, p in enumerate(fixtures) if mode == "fixture:" + str(p))
            assert actual[1:] == expected_fixtures[:index + 1]
        results.append({"mode": mode or "success", "exit": outcome.returncode,
                        "recorded_calls": len(actual)})
print(json.dumps({"status": "pass", "owned_modules": len(owned),
                  "fixture_imports": len(imports), "fixtures": len(fixtures),
                  "registered_pins": {name: len(entry["pins"]) for name, entry in registry.items()},
                  "fixture_paths": [str(p) for p in fixtures], "controls": results}, indent=2))
