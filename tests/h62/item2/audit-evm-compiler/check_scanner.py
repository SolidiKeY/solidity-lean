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
# Declaration delimiters must not consume assignments/arms inside the type.
edge_fixture="""namespace Edge
@[simp] theorem tupleProof : (0 : Nat) = (⟨0, by have h := True.intro; exact h⟩ : {n : Nat // True}).1 := by rfl
theorem rootLet : let x := 0; x = x := by rfl
theorem inlineMatch (x : Bool) : x = match x with
 | true => true
 | false => false := by cases x <;> rfl
theorem conditionalMatch (x : Bool) : x = if x then match x with
 | true => true
 | false => false
 else false := by cases x <;> rfl
end Edge
"""
with tempfile.TemporaryDirectory() as d:
 p=pathlib.Path(d)/'edges.lean';p.write_text(edge_fixture);edges=c.scan(p)
 assert len(edges)==4
 assert 'have h := True.intro' in edges[0]['source_signature']
 assert 'let x := 0; x = x' in edges[1]['source_signature']
 assert '| false => false' in edges[2]['source_signature']
 assert 'else false' in edges[3]['source_signature']
assert c.mask('a /- b /- c -/ d -/ e')=='a                   e'
try:c.mask('/- open')
except ValueError:pass
else:raise AssertionError('unterminated comment accepted')
print('PASS scanner boundary controls')
