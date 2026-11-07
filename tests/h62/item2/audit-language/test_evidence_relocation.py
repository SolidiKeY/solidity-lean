#!/usr/bin/env python3
"""Replay saved acceptance with relocated evidence and forbidden legacy reads.
No Lean invocation or new proof claim: fixtures use source bytes matching actual
saved kernel-check hashes. The checked historical source set is explicit.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[4]
SCRIPTS = ROOT / "scripts/h62/item2/audit-language"
BEFORE = "60f3df88d6dcb7b9dd1a31e9e8358e8348a01484"

HARNESS = r"""
import json, os, runpy, sys
from pathlib import Path
from unittest.mock import patch
legacy = Path(os.environ["H62_TEST_LEGACY_ROOT"]).resolve()
fixture = Path(os.environ["H62_TEST_FIXTURE"])
old_open = Path.open
def guarded_open(path, *args, **kwargs):
    if path.resolve().is_relative_to(legacy):
        raise AssertionError("legacy evidence read forbidden: " + str(path))
    return old_open(path, *args, **kwargs)
with patch.object(Path, "open", guarded_open):
    repair = fixture / "tests/h62/item2/audit-language/gate-repair-manifest.json"
    if os.environ["H62_TEST_MODE"] == "verify":
        evidence = Path(os.environ["H62_EVIDENCE"])
        sys.argv = [str(fixture / "scripts/h62/item2/audit-language/verify.py"),
                    "--census", str(evidence / "census.json"),
                    "--checks", str(evidence / "checks.json"),
                    "--gate-repair-manifest", str(repair),
                    "--output", str(evidence / "verified")]
        runpy.run_path(sys.argv[0], run_name="__main__")
    else:
        from retire_export import authenticate_resume_proofs
        receipts = json.loads((fixture / "tests/h62/item2/audit-language/received-overlays.json").read_text())
        authenticate_resume_proofs(receipts, repair)
        print("PASS-relocated-export-authentication")
"""

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--evidence", type=Path, required=True)
    p.add_argument("--work-root", type=Path, required=True)
    a = p.parse_args()
    a.evidence = a.evidence.resolve()
    a.work_root = a.work_root.resolve()
    assert not a.work_root.is_relative_to(ROOT), "test bulk must remain off Git"
    assert not a.work_root.is_relative_to(a.evidence), "relocation fixture must be outside the forbidden legacy root"
    a.work_root.mkdir(parents=True, exist_ok=True)
    results = []
    def git(*args):
        return subprocess.check_output(["git", *args], cwd=ROOT)
    def put(root, name, data):
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        return path
    with tempfile.TemporaryDirectory(prefix="relocation-", dir=a.work_root) as temporary:
        fixture = Path(temporary) / "checkout"
        evidence = Path(temporary) / "moved-evidence"
        for script in SCRIPTS.glob("*.py"):
            put(fixture, str(script.relative_to(ROOT)), script.read_bytes())
        owned = Path("tests/h62/item2/audit-language")
        for name in ["received-overlays.json", "gate-repair-manifest.json", "witness-index.json"]:
            put(fixture, str(owned / name), (ROOT / owned / name).read_bytes())
        receipts = json.loads((ROOT / owned / "received-overlays.json").read_text())
        legacy_roots = {Path(r["path"]).parents[len(Path(r["path_relative_to_evidence"]).parts) - 1] for r in receipts}
        assert len(legacy_roots) == 1
        legacy = legacy_roots.pop().resolve()
        assert not a.work_root.is_relative_to(legacy)
        for receipt in receipts:
            relative = receipt["path_relative_to_evidence"]
            put(evidence, relative, (a.evidence / relative).read_bytes())
        repair = json.loads((ROOT / owned / "gate-repair-manifest.json").read_text())
        for revision in repair["revisions"]:
            put(evidence, revision["patch_relative_to_evidence"], (a.evidence / revision["patch_relative_to_evidence"]).read_bytes())
            put(fixture, revision["path"], (ROOT / revision["path"]).read_bytes())
        census = a.evidence / "census-final/census.json"
        put(evidence, "census.json", census.read_bytes())
        checks = json.loads((a.evidence / "gate-repair-20261107/witnesses/checks.json").read_text())
        for i, check in enumerate(checks):
            current = (ROOT / check["file"]).read_bytes()
            if hashlib.sha256(current).hexdigest() != check["sha256"]:
                current = git("show", "c6f550e281a7e5affa9a99bc2cdaed556dec00e4:" + check["file"])
            assert hashlib.sha256(current).hexdigest() == check["sha256"], "fixture must match saved checked bytes"
            put(fixture, check["file"], current)
            original_log = a.evidence / Path(check["log"]).relative_to(legacy)
            log = put(evidence, "logs/" + str(i) + ".log", original_log.read_bytes())
            check["log"] = str(log)
        put(evidence, "checks.json", (json.dumps(checks) + "\n").encode())
        env = dict(os.environ, H62_EVIDENCE=str(evidence), H62_TEST_FIXTURE=str(fixture),
                   H62_TEST_LEGACY_ROOT=str(legacy), PYTHONPATH=str(fixture / "scripts/h62/item2/audit-language"),
                   GIT_DIR=git("rev-parse", "--absolute-git-dir").decode().strip(), GIT_WORK_TREE=str(fixture),
                   PYTHONDONTWRITEBYTECODE="1")
        def run(mode, label, expected=None):
            result = subprocess.run([sys.executable, "-c", HARNESS], cwd=ROOT,
                                    env=dict(env, H62_TEST_MODE=mode), capture_output=True, text=True)
            if expected is None:
                assert result.returncode == 0, result.stdout + result.stderr
            else:
                assert result.returncode != 0 and expected in result.stderr, result.stdout + result.stderr
                if expected != "legacy evidence read forbidden":
                    assert "legacy evidence read forbidden" not in result.stderr, "fallback attempted"
            results.append({"control": label, "exit": result.returncode,
                            "outcome": "pass" if expected is None else "expected-rejection"})
        # The same fixture reproduces both reported failures at the held head.
        for name in ["verify.py", "retire_export.py"]:
            put(fixture, "scripts/h62/item2/audit-language/" + name,
                git("show", BEFORE + ":scripts/h62/item2/audit-language/" + name))
        for mode in ["verify", "export"]:
            run(mode, "before-" + mode, "legacy evidence read forbidden")
        for name in ["verify.py", "retire_export.py"]:
            put(fixture, "scripts/h62/item2/audit-language/" + name, (SCRIPTS / name).read_bytes())
        for mode in ["verify", "export"]:
            run(mode, "relocated-" + mode)
        victim = evidence / receipts[1]["path_relative_to_evidence"]
        original = victim.read_bytes()
        victim.write_bytes(original + b"corrupt")
        for mode in ["verify", "export"]:
            run(mode, "corrupt-relocated-" + mode, "AssertionError")
        victim.unlink()
        for mode in ["verify", "export"]:
            run(mode, "missing-relocated-no-fallback-" + mode, "FileNotFoundError")
        victim.write_bytes(original)
        sys.path.insert(0, str(SCRIPTS))
        from overlay_review import receipt_patch_path
        with patch.dict(os.environ, {"H62_EVIDENCE": ""}):
            assert receipt_patch_path(receipts[0]) == Path(receipts[0]["path"])
        results.append({"control": "legacy-default-path-preserved", "outcome": "pass"})
        escape = evidence / "escape.patch"
        escape.symlink_to(Path(receipts[0]["path"]))
        for label, relative in [("absolute-path", receipts[0]["path"]),
                                ("parent-traversal", "../outside.patch"),
                                ("symlink-escape", "escape.patch")]:
            altered = dict(receipts[0], path_relative_to_evidence=relative)
            with patch.dict(os.environ, {"H62_EVIDENCE": str(evidence)}):
                try:
                    receipt_patch_path(altered)
                except ValueError:
                    results.append({"control": label, "outcome": "expected-rejection"})
                else:
                    raise AssertionError(label)
    lines = (ROOT / "tests/h62/item2/audit-language/registration-fragment.md").read_text().splitlines()
    start = lines.index("| Audit module | What it checks |")
    table = []
    for line in lines[start:]:
        if not line.startswith("|"):
            break
        table.append(line)
    assert len(table) == 7 and "FixedPointWitness.lean" in table[-1]
    results.append({"control": "five-registration-rows-in-one-table", "outcome": "pass"})
    (a.work_root / "results.json").write_text(json.dumps({"controls": results,
        "boundary": "Saved 51-witness acceptance fixture; no new Lean checks or proofs"}, indent=2) + "\n")
    print(json.dumps({"status": "PASS-relocation-regressions", "controls": len(results),
                      "results": str(a.work_root / "results.json")}))

if __name__ == "__main__":
    main()
