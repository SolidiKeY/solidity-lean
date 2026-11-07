#!/usr/bin/env python3
"""Static parser and evidence-boundary controls; no Lean invocation."""
import importlib.util
from pathlib import Path
import sys
sys.dont_write_bytecode = True
script = Path(__file__).resolve().parents[4] / 'scripts/h62/item6/migrate-source/h78-inventory.py'
spec = importlib.util.spec_from_file_location('h78_inventory', script)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
text = '''Lean.Expr.forallE `«name with space» (Lean.Expr.const `Nat [])
 (Lean.Expr.forallE `x (Lean.Expr.bvar 0) (Lean.Expr.bvar 1)
 (Lean.BinderInfo.instImplicit)) (Lean.BinderInfo.implicit)'''
r = m.telescope(text)
assert [b['binder_kind'] for b in r['binders']] == ['Lean.BinderInfo.implicit', 'Lean.BinderInfo.instImplicit']
assert r['binders'][0]['name_repr'] == '`«name with space»'
assert r['result_repr'] == '(Lean.Expr.bvar 1)'
assert m.application('Lean.Expr.const `X [Lean.Level.param `u]') == ['Lean.Expr.const', '`X', '[Lean.Level.param `u]']
for bad in ['Lean.Expr.forallE `x (Lean.Expr.bvar 0)', 'Lean.Expr.const `X [', '"unterminated']:
    try:
        m.telescope(bad)
    except ValueError:
        pass
    else:
        raise AssertionError('accepted malformed input')
assert m.family('X.noConfusion') == 'noConfusion'
assert m.family('X.match_2') == 'match_N'
assert m.family('_private.X.proof') == 'other_original_name'
print('PASS: balanced telescope/binder-kind parsing; malformed inputs rejected; name hints do not exempt private/hygienic candidates')

for label in ['full old ledger', 'partial old export', 'partial new export']:
    try:
        m.unique_rows([{'name': 'X'}, {'name': 'X'}], label)
    except ValueError:
        pass
    else:
        raise AssertionError('duplicate names accepted: ' + label)
print('PASS: duplicate-name negative controls for all three saved captures')
