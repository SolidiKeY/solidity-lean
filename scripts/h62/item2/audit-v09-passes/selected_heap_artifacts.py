#!/usr/bin/env python3
"""Verify H44 artifacts and run mandatory external acceptance.

Source-only tests need no external files. External acceptance always fails on
missing or changed evidence. Set VY3_AUDIT_ARTIFACTS to a staged artifact root.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[4]
MANIFEST = ROOT / "tests/h62/item2/audit-v09-passes/selected-heap-artifacts.json"


def artifact_root():
    configured = os.environ.get("VY3_AUDIT_ARTIFACTS")
    return Path(configured).resolve() if configured else ROOT / ".audit-artifacts/selected-heap"


def contained(root, relative):
    path = Path(relative)
    if path.is_absolute():
        raise ValueError("Manifest paths must be relative")
    target = (root / path).resolve()
    target.relative_to(root.resolve())
    return target


def artifact(name):
    entries = json.loads(MANIFEST.read_text())["files"]
    matches = [entry for entry in entries if Path(entry["repository_path"]).name == name]
    if len(matches) != 1:
        raise ValueError("Expected one manifest entry for " + name)
    entry = matches[0]
    path = contained(artifact_root(), entry["path"])
    try:
        data = path.read_bytes()
    except FileNotFoundError as error:
        raise FileNotFoundError("Stage H44 artifacts and set VY3_AUDIT_ARTIFACTS: " + str(path)) from error
    if len(data) != entry["bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
        raise ValueError("Artifact hash or size mismatch: " + name)
    return entry, data


def materialize(entry, data):
    target = contained(ROOT, entry["repository_path"])
    if target.exists() and target.read_bytes() != data:
        raise ValueError("Refusing to overwrite different local work: " + str(target))
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--materialize", action="store_true")
    parser.add_argument("--acceptance", action="store_true",
                        help="required full accounting check: portable suite plus external ledger assertions")
    args = parser.parse_args()
    for name in ("SelectedHeapBoundaryWitness.lean", "selected-heap-witness-map.json"):
        entry, data = artifact(name)
        if args.materialize:
            materialize(entry, data)
        print("verified", entry["sha256"], entry["path"], flush=True)
    if args.acceptance:
        tests = "tests/h62/item2/audit-v09-passes"
        subprocess.run([sys.executable,"-m","unittest","discover","-s",tests,"-p","test_*.py"],cwd=ROOT,check=True)
        subprocess.run([sys.executable,tests+"/selected_heap_external_checks.py"],cwd=ROOT,check=True)

if __name__ == "__main__":
    main()
