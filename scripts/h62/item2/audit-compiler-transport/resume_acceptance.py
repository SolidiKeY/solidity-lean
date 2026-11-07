#!/usr/bin/env python3
"""Meaningful lexical regressions and original/current frozen-source checks."""
import argparse
import json
from pathlib import Path
import re
from census import BASE, declarations, digest
from rebaseline import snapshot, compare, git

ap=argparse.ArgumentParser();ap.add_argument('--ref',required=True)
ap.add_argument('--historical',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args();root=Path.cwd()
fixture="""namespace Outer
mutual
theorem f : (n : Nat) → n = n
  | 0 => rfl
  | n+1 => rfl
end
@[simp] theorem _root_.Absolute.g (n : Nat := 2) :
    (match n with | 0 => True | _ => True) := by trivial
theorem matching (n : Nat) :
    match n with
    | 0 => True
    | _ => True := by cases n <;> trivial
-- theorem masked : False := nope
def quote := "theorem quoted : False := nope"
/- theorem gone : False := /- nested -/ nope -/
end Outer
"""
rows=declarations(fixture,'Fixture.lean')
assert [r['source_name']for r in rows]==['Outer.f','Absolute.g','Outer.matching']
assert rows[0]['signature']=='theorem f : (n : Nat) → n = n'
assert rows[1]['signature'].endswith('(match n with | 0 => True | _ => True)')
assert rows[2]['signature'].endswith('| _ => True')
original=snapshot(root,BASE);current=snapshot(root,a.ref);transition=compare(original,current)
assert transition['summary']=={'original_modules':122,'current_modules':134,'original_theorems':560,'current_theorems':808,'retained':560,'unchanged_signatures':560,'unchanged_module_bytes':560,'added':248,'removed':0}
# Independent token counter, separately implemented comment/string masking.
def uncomment(text):
    pattern=re.compile(r'/\-|\-/|--[^\n]*|"(?:\\.|[^"\\])*"',re.S)
    depth,prev,chunks=0,0,[]
    for m in pattern.finditer(text):
        if depth==0:chunks.append(text[prev:m.start()])
        token=m.group()
        if token=='/-':depth+=1
        elif token=='-/' and depth:depth-=1
        prev=m.end()
    assert depth==0
    chunks.append(text[prev:]);return ''.join(chunks)
for view in [original,current]:
    for entry in view['modules']:
        body=git(root,'show',view['commit']+':'+entry['module']).decode()
        assert len(re.findall(r'\btheorem\s+[^\s:({]+',uncomment(body)))==entry['theorems'],entry['module']
# Compare against actual preserved historical evidence, not two new scans.
historical=json.loads(a.historical.read_text());assert historical['base']==BASE
assert historical['modules']==original['modules']
old={r['id']:r for r in historical['statements']};new={r['id']:r for r in original['statements']}
assert set(old)==set(new)
corrections=[]
for key in sorted(old):
    assert old[key]['source_name']==new[key]['source_name']
    if old[key]['signature_sha256']!=new[key]['signature_sha256']:
        corrections.append({'source_name':new[key]['source_name'],'historical_signature_sha256':old[key]['signature_sha256'],'corrected_signature_sha256':new[key]['signature_sha256'],'reason':'historical scanner consumed equation proof text until a later :=; source/module bytes are identical','original_module_sha256':next(r['sha256']for r in original['modules']if r['module']==new[key]['module'])})
assert {r['source_name']for r in corrections}=={'Solidity.Backend.Passes.typed_sequencing_assoc','Solidity.Backend.Passes.MemoryJoinCost.cost_join','Solidity.Backend.Passes.MemoryJoinFrame.frame_join'}
result={'schema_version':1,'status':'pass','historical_evidence':str(a.historical),'historical_evidence_sha256':digest(a.historical.read_bytes()),'transition':transition['summary'],'lexical_metadata_corrections':corrections,'boundary':'Scanner metadata only. Original proof evidence remains historical; current Lean replay/domain audit pending.'}
a.output.write_text(json.dumps(result,indent=2)+'\n')
print('PASS mutual/root/equation/default-binder/match-type/comment/string regressions; independent per-file counts; retained560/added248;3 historical metadata corrections, unchanged module bytes')
