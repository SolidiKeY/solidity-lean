#!/usr/bin/env python3
"""Regression for confirmed comment-import bugs, without Lean or a server."""
import pathlib,sys
root=pathlib.Path(__file__).resolve().parents[3]
sys.path.insert(0,str(root/'scripts/h55/source-relations'))
from lean_imports import header_imports
assert header_imports('/- nested /- import Fake -/ comment -/\nimport A.B C.D\n-- import Wrong\nimport E.F\nnamespace X\nimport NotHeader')==['A.B','C.D','E.F']
assert header_imports('import A/-comment-/B\nnamespace X')==['A','B']
assert header_imports('prelude\nimport Init.Prelude\n/-! import Wrong -/\ndef x := 1')==['Init.Prelude']
for name,bogus in [('Solidity/Source/Units.lean','and'),('Solidity/Frontend/Static/Units.lean','targets')]:
    actual=header_imports((root/name).read_text())
    assert actual and bogus not in actual,(name,actual)
print('H55_IMPORT_SCANNER_PASS: nested comments, multi-imports, prelude, real prose regressions')
