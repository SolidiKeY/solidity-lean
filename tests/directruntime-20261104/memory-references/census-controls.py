"""Guard regression: tampered or truncated provenance must not pass the census.

Use isolated manifest copies; never mutate the producer, executable, generated
C or source. These refusal controls are development evidence, not proof of a
runtime trust property. Require an actual successful census first.
"""
import copy
import hashlib
import json
import pathlib
import subprocess
import sys
import tempfile

repo, prefix, native, baseline, out = [pathlib.Path(x).resolve() for x in sys.argv[1:]]
script = pathlib.Path(__file__).with_name("runtime-boundary-census.py")
summary = json.loads((baseline/"summary.json").read_text())
assert summary["censusScriptSha256"] == hashlib.sha256(script.read_bytes()).hexdigest()
assert summary["binarySha256"] == hashlib.file_digest((native/"direct-check").open("rb"), "sha256").hexdigest()
out.mkdir(parents=True, exist_ok=False)
manifest = json.loads((native/"build.json").read_text())
rows = []
for case in ["truncated-source-manifest", "wrong-binary-fingerprint", "wrong-build-input-fingerprint", "truncated-build-inputs", "python-optimization"]:
    with tempfile.TemporaryDirectory(dir=out) as directory:
        root = pathlib.Path(directory)
        staged = root/"native"
        staged.mkdir()
        (staged/"direct-check").symlink_to(native/"direct-check")
        altered = copy.deepcopy(manifest)
        if case == "truncated-source-manifest":
            altered["sourceFiles"].pop()
        elif case == "wrong-binary-fingerprint":
            altered["executable"] = "0"*64
        elif case == "wrong-build-input-fingerprint":
            altered["buildInputs"][next(iter(altered["buildInputs"]))] = "0"*64
        elif case == "truncated-build-inputs":
            altered["buildInputs"].pop(str(repo/"scripts/build-direct-native.py"))
        (staged/"build.json").write_text(json.dumps(altered))
        command = [sys.executable] + (["-O"] if case == "python-optimization" else []) + [str(script), str(repo), str(prefix), str(staged), str(root/"census")]
        run = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
        assert run.returncode != 0, case
        expected = "RuntimeError: Census checks require ordinary Python" if case == "python-optimization" else "AssertionError"
        assert expected in run.stderr, (case, run.stderr)
        (out/(case+".stderr")).write_text(run.stderr)
        rows.append({"case": case, "exit": run.returncode, "expectedRefusal": True, "stderrSha256": hashlib.sha256(run.stderr.encode()).hexdigest()})
(out/"results.json").write_text(json.dumps({"controls": rows, "baseline": str(baseline), "boundary": "Rejects these five provenance-tampering cases; no exhaustive runtime absence certification."}, indent=2)+"\n")
print("PASS five census provenance refusal controls")
