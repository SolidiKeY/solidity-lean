#!/usr/bin/env python3
"""Acceptance for extraction boundaries, frozen counts and reproducibility."""
import importlib.util, json, pathlib, tempfile
ROOT=pathlib.Path(__file__).resolve().parents[4]
p=ROOT/'scripts/h62/item2/audit-evm-compiler/census.py'
s=importlib.util.spec_from_file_location('census',p); c=importlib.util.module_from_spec(s);s.loader.exec_module(c)
fixture="""namespace A
/- theorem fake : False := by /- nested -/ exact bad -/
def text := "theorem fake2 : False := bad"
mutual
@[simp] theorem first : ∀ n : Nat, n = n
 | 0 => rfl
 | n+1 => rfl
end
@[simp] private theorem hidden (x : Nat) : x = x := rfl
section
variable {x : Nat}
omit x in
theorem next : 0 = 0 := rfl
end
protected theorem last : True := True.intro
end A
"""
with tempfile.TemporaryDirectory() as d:
 p=pathlib.Path(d)/'fixture.lean'; p.write_text(fixture); rows=c.scan(p)
 assert [r['candidate_name'] for r in rows]==['A.first','A.hidden','A.next','A.last']
 assert rows[1]['visibility']=='private'
 assert all(r['source_signature'].count('theorem')==1 for r in rows)
 assert rows[2]['preceding_context_command_history']==['variable {x : Nat}','omit x in']
 assert rows[3]['preceding_context_command_history']==[]
assert c.mask('a /- b /- c -/ d -/ e')=='a                   e'
try:c.mask('/- open')
except ValueError:pass
else:raise AssertionError('unterminated comment accepted')
print('PASS scanner boundary controls')
