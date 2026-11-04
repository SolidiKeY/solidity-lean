#!/usr/bin/env python3
"""Black-box cross-file, masked-reference, and uncertainty controls."""
import json
import pathlib
import subprocess
import sys
root = pathlib.Path(__file__).resolve().parents[3]
files = [{"path": "A.lean", "text": "theorem a : True := by trivial\ntheorem unused : True := by trivial\n-- unused\n"}, {"path": "B.lean", "text": "def use := a\n\"a unused\"\n"}]
p = subprocess.run([sys.executable, str(root / "scripts/h28-terra/proof-cleanup/item3.py")], input=json.dumps({"files": files}), capture_output=True, text=True, check=True)
v = "candidate-only-public-and-dynamic-review-required"
assert json.loads(p.stdout) == [{"path": "A.lean", "declarations": [{"name": "a", "lexicalOccurrences": 2, "verdict": v}, {"name": "unused", "lexicalOccurrences": 1, "verdict": v}]}, {"path": "B.lean", "declarations": [{"name": "use", "lexicalOccurrences": 1, "verdict": v}]}]
print("cross-file references, masked text, and uncertainty controls passed")
