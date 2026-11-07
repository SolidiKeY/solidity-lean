"""Guard regression: missing/overlapping link ranges or tampered provenance fail.

Exercise the real diagnostic replay map and isolated manifest/ELF copies.
No production input is changed and no successful verifier verdict is inferred.
"""
import importlib.util
import json
import pathlib
import subprocess
import sys
import tempfile

repo, prefix, native, census, replay, out = [pathlib.Path(p).resolve() for p in sys.argv[1:]]
script = pathlib.Path(__file__).with_name("linker-attribution.py")
spec = importlib.util.spec_from_file_location("attribution", script)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
result = json.loads((replay/"replay.json").read_text())
assert result["byteIdentical"] and result["attributedTextRows"] == 8405 and result["unattributedTextRows"] == 0
out.mkdir(parents=True, exist_ok=False)
rows = [json.loads(line) for line in (census/"defined-symbols.jsonl").read_text().splitlines()]
rows = [r for r in rows if r["type"] in "TtWwIi"]
lines = (replay/"link.map").read_text().splitlines(True)
startup = next(line for line in lines if "/lib/Scrt1.o:(.text)" in line)
controls = []
for case in ["missing-startup-range", "overlapping-startup-range"]:
    changed = [line for line in lines if line != startup] if case.startswith("missing") else [item for line in lines for item in ([line, line] if line == startup else [line])]
    path = out/(case+".map")
    path.write_text("".join(changed))
    try:
        helper.attribute(rows, helper.load_map(path))
    except AssertionError as error:
        controls.append({"case": case, "expectedRefusal": True, "reason": str(error)})
    else:
        raise AssertionError("Tampered map accepted: "+case)
for case in ["truncated-build-inputs", "changed-original-elf", "changed-census-fingerprint", "python-optimization"]:
    with tempfile.TemporaryDirectory(dir=out) as directory:
        root = pathlib.Path(directory)
        staged = root/"native"
        staged.mkdir()
        manifest = json.loads((native/"build.json").read_text())
        if case == "truncated-build-inputs":
            manifest["buildInputs"].pop(next(iter(manifest["buildInputs"])))
        if case == "changed-original-elf":
            (staged/"direct-check").write_bytes(b"tampered ELF")
        else:
            (staged/"direct-check").symlink_to(native/"direct-check")
        (staged/"build.json").write_text(json.dumps(manifest))
        selected_census = census
        if case == "changed-census-fingerprint":
            selected_census = root/"census"
            selected_census.mkdir()
            (selected_census/"summary.json").write_bytes((census/"summary.json").read_bytes()+b" ")
        command = [sys.executable]+(["-O"] if case == "python-optimization" else [])+[str(script), str(repo), str(prefix), str(staged), str(selected_census), str(root/"result")]
        run = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=30)
        assert run.returncode != 0, case
        assert ("RuntimeError: Attribution requires ordinary Python checks" if case == "python-optimization" else "AssertionError") in run.stderr
        (out/(case+".stderr")).write_text(run.stderr)
        controls.append({"case": case, "exit": run.returncode, "expectedRefusal": True})
(out/"results.json").write_text(json.dumps({"controls": controls, "baseline": str(replay), "boundary": "Six attribution refusal controls, not semantic absence certification."}, indent=2)+"\n")
print("PASS six linker-attribution refusal controls")
