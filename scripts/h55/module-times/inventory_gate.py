#!/usr/bin/env python3
"""Fail-closed structural check for a reviewed H55 inventory.

This compares a supplied inventory against the current census; it does not
establish that execution recipes, context decisions, or measurements are valid.
"""
import importlib.util
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("h55_census", ROOT / "scripts/h55/module-times/census.py")
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)
HEX = re.compile(r"[0-9a-f]{64}\Z")


def validate(current, manifest):
    if not isinstance(current, list) or not current or not isinstance(manifest, list):
        return ["invalid or empty inventory"]
    expected = {}
    for row in current:
        if not isinstance(row, dict) or not isinstance(row.get("path"), str) or not isinstance(row.get("sha256"), str):
            return ["invalid census"]
        if row["path"] in expected or not HEX.fullmatch(row["sha256"]):
            return ["duplicate or invalid census entry"]
        expected[row["path"]] = row["sha256"]
    errors, seen = [], set()
    for row in manifest:
        if not isinstance(row, dict) or not isinstance(row.get("path"), str):
            errors.append("invalid inventory entry")
            continue
        path = row["path"]
        if path in seen:
            errors.append(f"duplicate: {path}")
        seen.add(path)
        if path not in expected:
            errors.append(f"unexpected: {path}")
        elif row.get("sha256") != expected[path]:
            errors.append(f"source hash mismatch: {path}")
        if row.get("context") not in ("root", "bridge"):
            errors.append(f"undecided context: {path}")
        if row.get("method") not in ("module", "file-check"):
            errors.append(f"undecided method: {path}")
    errors.extend(f"missing: {p}" for p in sorted(expected.keys() - seen))
    return errors


def main():
    if len(sys.argv) != 2:
        print("usage: inventory_gate.py INVENTORY.json", file=sys.stderr)
        return 2
    try:
        manifest = json.loads(pathlib.Path(sys.argv[1]).read_text())
        # Git diff can trust index flags and miss worktree changes.
        flags = subprocess.check_output(["git", "ls-files", "-v", "-z", "--", "*.lean"], cwd=ROOT)
        if any(not entry.startswith(b"H ") for entry in flags.split(b"\0") if entry):
            raise ValueError("Lean index has unverified flags or stages")
        # Compare HEAD to the index and worktree separately: staged edits can
        # otherwise be cancelled by opposite unstaged edits.
        dirty = subprocess.run(["git", "diff", "--quiet", "HEAD", "--", "*.lean"], cwd=ROOT).returncode
        staged = subprocess.run(["git", "diff", "--cached", "--quiet", "HEAD", "--", "*.lean"], cwd=ROOT).returncode
        if dirty or staged:
            raise ValueError("tracked Lean source differs from HEAD")
        untracked = subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard", "-z", "--", "*.lean"], cwd=ROOT)
        if untracked:
            raise ValueError("untracked Lean source present")
        errors = validate(census.census(ROOT), manifest)
    except (OSError, UnicodeError, ValueError, subprocess.CalledProcessError) as exc:
        print(f"inventory unavailable: {exc}", file=sys.stderr)
        return 1
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print("inventory rows structurally complete; decisions and execution are not authenticated")
    return 0


if __name__ == "__main__":
    sys.exit(main())
