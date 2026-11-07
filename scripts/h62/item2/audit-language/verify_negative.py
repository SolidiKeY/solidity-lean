#!/usr/bin/env python3
"""Reproduce the reviewers' witness-reassignment attack; require rejection.
Only the index read is substituted in memory. No theorem, log or file changes.
"""
import argparse
import json
from pathlib import Path
import runpy
import sys
from unittest.mock import patch

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("--census", type=Path, required=True)
p.add_argument("--checks", type=Path, required=True)
p.add_argument("--gate-repair-manifest", type=Path)
args = p.parse_args()
root = Path(__file__).resolve().parents[4]
index_path = root / "tests/h62/item2/audit-language/witness-index.json"
index = json.loads(index_path.read_text())
index[3]["witness"] = index[0]["witness"]
original_read = Path.read_text

def substituted_read(path, *positional, **named):
    if path.resolve() == index_path.resolve(): return json.dumps(index)
    return original_read(path, *positional, **named)

sys.argv = [str(Path(__file__).with_name("verify.py")), "--census", str(args.census),
            "--checks", str(args.checks), "--output", str(args.checks.parent / "negative-unexpected")]
if args.gate_repair_manifest:
    sys.argv += ["--gate-repair-manifest", str(args.gate_repair_manifest)]
try:
    with patch.object(Path, "read_text", substituted_read):
        runpy.run_path(sys.argv[0], run_name="__main__")
except AssertionError as error:
    expected = "H62_WITNESS " + index[3]["witness"] + " FOR " + index[3]["target"]
    assert str(error) == expected, str(error)
    print(json.dumps({"status": "PASS", "negative_control": "wrong-witness-association-rejected", "missing_receipt": expected}))
else:
    raise AssertionError("wrong witness association was accepted")
