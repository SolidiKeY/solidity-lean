#!/usr/bin/env python3
"""Emit the old one-stage simplification as an isolated negative control.
Run emitted file on both versions: v4.24.0 passes, v4.35.0 must fail.
The staged fixture itself must pass on both. No production edits.
"""
import pathlib, sys
root=pathlib.Path(__file__).resolve().parents[4]
s=(root/'tests/h62/item6/migrate-language/DecideFixture.lean').read_text()
old="[Bounds.inRange, Bool.and_eq_true, decide_eq_true_eq]\n  unfold Bounds.lower Bounds.upper"
assert s.count(old)==1
s=s.replace(old,"[Bounds.inRange, Bounds.lower, Bounds.upper, Bool.and_eq_true, decide_eq_true_eq]")
pathlib.Path(sys.argv[1]).write_text(s)
