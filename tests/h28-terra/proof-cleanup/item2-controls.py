#!/usr/bin/env python3
"""Independent black-box controls for cross-file exact duplicate candidates."""
import json
import pathlib
import subprocess
import sys

root = pathlib.Path(__file__).resolve().parents[3]
program = root / "scripts/h28-terra/proof-cleanup/item2.py"

def invoke(files):
    proc = subprocess.run([sys.executable, str(program)], input=json.dumps({"files": files}), text=True, capture_output=True, check=True)
    return json.loads(proc.stdout)

files = [
    {"path": "A.lean", "text": "theorem first : True := by trivial\ntheorem different : True := by exact True.intro\n"},
    {"path": "B.lean", "text": "lemma second : True := by trivial\n"},
    {"path": "C.lean", "text": "def empty"},
]
assert invoke(files) == [
    {"path": "A.lean", "duplicateCandidates": [["A.lean:first", "B.lean:second"]]},
    {"path": "B.lean", "duplicateCandidates": [["A.lean:first", "B.lean:second"]]},
    {"path": "C.lean", "duplicateCandidates": []},
]
assert invoke([]) == []
assert invoke([files[0], files[0]]) == {"error": "invalid-or-duplicate-files"}
print("cross-file, different-body, empty, and duplicate-input controls passed")
