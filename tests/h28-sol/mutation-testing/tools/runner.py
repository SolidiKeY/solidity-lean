#!/usr/bin/env python3
"""Disposable-tree mutation runner with a separate assignment acceptance boundary.

The manifest is executable trusted test configuration, never production input.
The engine requires checked source-linked semantic witnesses for kills.
Infrastructure failures are never kills; pilot completion is not scope acceptance.
"""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess


def digest(data):
    return hashlib.sha256(data).hexdigest()


def relative(path):
    p = Path(path)
    if p.is_absolute() or not p.parts or ".." in p.parts:
        raise ValueError("unsafe relative path: " + str(path))
    return p


def mutate(tree, case):
    path = tree / relative(case["target"])
    if path.is_symlink() or not path.is_file():
        raise ValueError("target must be a regular file")
    before = path.read_bytes()
    if digest(before) != case["target_sha256"]:
        raise ValueError("target hash mismatch")
    old, new = case["old"].encode(), case["new"].encode()
    if not old or old == new or before.count(old) != 1:
        raise ValueError("mutation must replace exactly one unique nonempty span")
    after = before.replace(old, new, 1)
    path.write_bytes(after)
    diff = "".join(difflib.unified_diff(before.decode().splitlines(True),
                       after.decode().splitlines(True),
                       fromfile="a/" + case["target"], tofile="b/" + case["target"]))
    return {"before_sha256": digest(before), "after_sha256": digest(after),
            "diff_sha256": digest(diff.encode()), "diff": diff}


def classify(compilation, oracle, log, allowed):
    if compilation["kind"] != "exit":
        return compilation["kind"]
    if compilation["exit"] != 0:
        return "invalid-compilation" if compilation["exit"] == 1 else "error"
    if oracle is None:
        return "unrun"
    if oracle["kind"] != "exit":
        return oracle["kind"]
    if oracle["exit"] == 0:
        return "surviving"
    if oracle["exit"] != 1:
        return "error"
    if re.search(r"out of memory|oom|killed|crash|segmentation|stack overflow|timeout|timed out|panic", log, re.I):
        return "error"
    # Every Lean error line must be attributed to a predeclared oracle location.
    # An arbitrary nonzero exit or a matching substring never suffices.
    errors = [line for line in log.splitlines() if re.search(r"(?:^|: )error:", line)]
    if not errors or not allowed:
        return "error"
    if len(errors) == len(allowed) and all(
            sum(bool(re.fullmatch(pattern, line)) for line in errors) == 1 for pattern in allowed) and all(
            sum(bool(re.fullmatch(pattern, line)) for pattern in allowed) == 1 for line in errors):
        # A proof rejection is not yet a checked semantic kill witness.
        return "oracle-rejected-unvalidated"
    return "error"


def summary(records, expected):
    from engine import summarize
    return summarize(records, expected)


def run(repo, manifest, out, manifest_path=None):
    if manifest.get("schema") != 2 or manifest.get("state") != "frozen":
        raise ValueError("committed frozen schema-2 manifest required")
    if manifest_path is None:
        raise ValueError("committed manifest path required")
    from engine import run_frozen
    return run_frozen(repo, manifest, out, Path(manifest_path).resolve())


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    root = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
    result = run(root, json.loads(args.manifest.read_text()), args.output.resolve(), args.manifest)
    print(json.dumps({key: value for key, value in result.items() if key != "records"}, indent=2))
    raise SystemExit(0 if result["runner_cases_complete"] else 1)
