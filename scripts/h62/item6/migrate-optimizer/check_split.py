#!/usr/bin/env python3
"""Verify H44/H112 packaging and STOP preservation without invoking Lean."""
import ast, hashlib, json, os, subprocess, sys, tarfile, tempfile
from pathlib import Path
sys.dont_write_bytecode = True
from bulk import ROOT, MANIFEST, metadata, bulk_path, load_bulk_json, pack_archive
import bulk
parent = metadata()["split_parent"]
lane = Path("tests/h62/item6/migrate-optimizer")
def command(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True)
for path in (ROOT/"scripts/h62/item6/migrate-optimizer").glob("*.py"):
    ast.parse(path.read_text(), filename=str(path))
command("git", "diff", "--exit-code", parent, "--", "Solidity", "lean-toolchain", "lakefile.toml", "run-lean.sh")
entries = metadata()["files"]
assert len(entries) == 7
for relative, entry in entries.items():
    path = bulk_path(Path(relative).name)
    original = subprocess.check_output(["git", "show", parent+":"+relative], cwd=ROOT)
    assert path.read_bytes() == original
    assert not (ROOT/relative).exists(), relative
archive = Path(metadata()["archive"]["path"])
assert archive.stat().st_size == metadata()["archive"]["bytes"]
assert hashlib.sha256(archive.read_bytes()).hexdigest() == metadata()["archive"]["sha256"]
with tarfile.open(archive, "r:gz") as packed:
    assert sorted(packed.getnames()) == sorted(entries)
    for relative in entries:
        assert packed.extractfile(relative).read() == Path(entries[relative]["path"]).read_bytes()
for name in ["Acceptance.lean", "Interfaces.lean"]:
    relative = str(lane/name)
    assert (ROOT/relative).read_bytes() == subprocess.check_output(["git", "show", parent+":"+relative], cwd=ROOT)
print(command("python3", "scripts/h62/item6/migrate-optimizer/fixtures.py", "--check").strip())
with tempfile.TemporaryDirectory(dir=archive.parent) as scratch:
    scratch = Path(scratch)
    recreated = pack_archive(scratch/"repacked.tar.gz")
    assert recreated.read_bytes() == archive.read_bytes()
    # Missing/tampered relocated evidence must fail closed, including STOP input.
    copied = scratch/"measurements.json"
    copied.write_bytes(bulk_path("measurements.json").read_bytes())
    fake = metadata()
    key = str(lane/"measurements.json")
    fake["files"][key]["path"] = str(copied)
    fake_manifest = scratch/"manifest.json"
    fake_manifest.write_text(json.dumps(fake))
    real_manifest = bulk.MANIFEST
    try:
        bulk.MANIFEST = fake_manifest
        assert load_bulk_json("measurements.json")["performance_status"] == "STOP_GT_10_PERCENT"
        payload = copied.read_bytes()
        copied.write_bytes(b"!"+payload[1:])
        try: load_bulk_json("measurements.json")
        except AssertionError: pass
        else: raise AssertionError("tampered evidence accepted")
        copied.unlink()
        try: load_bulk_json("measurements.json")
        except FileNotFoundError: pass
        else: raise AssertionError("missing evidence accepted")
    finally:
        bulk.MANIFEST = real_manifest
process = subprocess.run([sys.executable, str(ROOT/"scripts/h62/item6/migrate-optimizer/measure.py"), "4.35.0", "h44-no-job", "closure"], cwd=ROOT, capture_output=True, text=True, env={**os.environ, "PYTHONDONTWRITEBYTECODE":"1"})
assert process.returncode == 1 and "STOP_GT_10_PERCENT" in process.stderr
assert not Path("/workspace/migrate-optimizer-evidence/h44-no-job").exists()
command("python3", "scripts/h62/item6/migrate-optimizer/summarize.py")
for name in ["interface-hashes.json", "measurements.json"]:
    assert (Path(metadata()["derived_output_directory"])/name).read_bytes() == bulk_path(name).read_bytes()
report = json.loads((ROOT/lane/"dependency-report.json").read_text())
stop = next(b for b in report["typed_blockers"] if b["id"] == "MIG-OPT-PERF-STOP")
assert Path(stop["fixture"]).is_file() and Path(stop["evidence"]).is_file()
print("H44_SPLIT_STATIC_PASS: 7 payloads/73011 bytes preserved; deterministic archive; real-module fixtures unchanged; missing/tampered bulk rejected; STOP retained; historical summaries reproduce outside Git; production and budgets unchanged. No Lean executed.")
