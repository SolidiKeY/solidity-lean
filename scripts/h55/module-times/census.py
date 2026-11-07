#!/usr/bin/env python3
"""Enumerate every Git-tracked Lean path; classifications are not exclusions."""
import hashlib
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]


def classify(path):
    if path.startswith("Solidity/Examples/"):
        return "examples"
    if path.startswith("Solidity/"):
        return "core"
    if path.startswith("Bridge/vendor/") or path.startswith("vendor/"):
        return "vendor-review"
    if path.startswith("Bridge/tests/"):
        return "bridge-control-review"
    if path.startswith("Bridge/"):
        return "bridge"
    if path.startswith("tests/") or path.startswith("scripts/"):
        return "control-check-review"
    return "root-or-other-review"


def census(root):
    tracked = subprocess.check_output(["git", "ls-files", "-z", "--", "*.lean"], cwd=root)
    paths = [p.decode("utf-8") for p in tracked.split(b"\0") if p]
    if not paths or len(paths) != len(set(paths)):
        raise ValueError("empty or duplicate tracked path list")
    rows = []
    for path in sorted(paths):
        p = root / path
        if p.is_symlink() or not p.is_file():
            raise ValueError(f"missing, non-file or symlink: {path}")
        rows.append({"path": path, "category": classify(path),
                     "sha256": hashlib.sha256(p.read_bytes()).hexdigest()})
    return rows


def main():
    if len(sys.argv) != 1:
        print("usage: census.py", file=sys.stderr)
        return 2
    try:
        print(json.dumps(census(ROOT), indent=2))
    except (OSError, UnicodeError, ValueError, subprocess.CalledProcessError) as exc:
        print(f"census failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
