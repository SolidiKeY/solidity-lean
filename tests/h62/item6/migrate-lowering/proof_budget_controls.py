#!/usr/bin/env python3
"""Controls for false budget/tactic evidence and mixed decide modes."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[4]/"scripts/h62/item6/migrate-lowering"))
from proof_budgets import classify
fake=classify('/- set_option maxHeartbeats 0 /- decide +native -/ -/\ndef s := "set_option maxRecDepth 0; decide +kernel"\n-- native_decide\ndef «decide» := 1\n')
assert fake["budget_class"]=="no-explicit-source-option"
assert not fake["explicit_options"] and not fake["decide_occurrences"] and not fake["features"]["native_decide"]
r=classify('example : True := by decide\nexample : True := by decide +revert +kernel\nset_option maxHeartbeats 100 in\nexample : True := by decide +native\n')
assert r["decide_modes"]==["default-candidate","kernel-flag","native-flag"]
assert r["explicit_options"][0]["value_text"]=="100"
assert r["budget_class"]=="explicit-source-option"
assert not classify('def x := Decidable.decide True')["decide_occurrences"]
assert classify('def x := decide (1 = 1)')["decide_occurrences"][0]["lexical_context"]=="term-application-candidate"
print("PASS: nested comments/string/quoted-name masking, qualified references, modifier chains, and explicit-option classification")
