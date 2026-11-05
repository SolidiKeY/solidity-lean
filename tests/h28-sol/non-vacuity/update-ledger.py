#!/usr/bin/env python3
"""Refresh source-complete constructor clauses and current evidence dispositions.
Open semantic rows remain open; this is not acceptance generation.
"""
import fcntl,hashlib,json,pathlib,re
here=pathlib.Path(__file__).resolve().parent; root=here.parents[2]
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
p=here/'inventory.json'; d=json.loads(p.read_text())
def ws(module,*names): return [{'file':f'tests/h28-sol/non-vacuity/lean/Solidity/Assurance/NonVacuityH28/{module}.lean','name':'Solidity.Assurance.NonVacuityH28.'+n} for n in names]
def mark(row,module,*names):
 row.update(status='witnessed',witnesses=ws(module,*names));row.pop('finding',None)
main={
'rule_sound':('Calculus','assertion_rule_semantics'), 'rule_unique':('Families','unique_family','every_rule_inhabited'),
'rule_is_step':('Families','rule_step_family','every_rule_inhabited'), 'rule_exists':('Families','every_rule_inhabited'),
'rule_of_step':('Families','rule_from_step_family','every_rule_inhabited'),
'solkey_rule_exists':('Calculus','solkey_rule_application'), 'solkey_rule_lt_calculus':('Calculus','zero_unwind_strict'),
'solkey_step_taclet':('Calculus','solkey_admission_application'), 'solkey_eq_calculus':('Calculus','solkey_equivalence'),
'solkey_lt_calculus':('Calculus','solkey_strict'), 'soundness':('Calculus','calculus_application','assertion_derivation','assertion_runs'),
"soundness'":('Calculus','direct_application','assertion_derivation','assertion_runs'),
'solkey_soundness':('Calculus','solkey_application','assertion_derivation','assertion_runs'),
'callback_soundness':('Callbacks','payment_headline','payment_derivation','callback_program_resume','top_callback_policy'),
'noCallback_soundness':('Callbacks','noCallback_payment_headline','noCallback_payment_derivation','callback_program_noCallback','top_callback_policy'),
'noCallback_iff':('Calculus','noCallback_equivalence','assertion_runs'),
'cleanTail_holds':('TailSensitive','tail_clean_main','tail_clean_source','tail_premise_cannot_be_erased'),
'symex_sound':('Calculus','symex_application','symex_actual_progress','assertion_runs'),
'compiler_correct':('Families','correct_success','correct_revert','closed_joint_witness'),
'compiler_net':('JointWorld','joint_payment_compiler_application','joint_payment_world'),
'compiler_checked':('CheckedFamilies','checked_families_joint')}
for row in d['theorems']:
 args=main[row['theorem'].removeprefix('Solidity.Main.')];mark(row,*args);mark(row['original'],*args)
 row['original']['application_boundary']='The exact Main wrapper delegates to this original; wrapper application is kernel-checked. Signature/axioms of both are independently reported.'
branches={'core':('Families','checked_family','closed_joint_witness'),'memory':('MemoryInputs','primitive_input','primitive_joint'),'construction':('CheckedObjects','construction_input','construction_joint')}
for row in d['checked_branches']:
 args=branches.get(row['constructor'],('CheckedFamilies','checked_families_joint'));mark(row,*args)
 row['coverage_boundary']='Public Input/Rep contract inhabitation only; no producer repair or operation-completeness claim.'
controls={
'always-revert':('Families','always_revert_rejected'), 'empty-fragment-acceptance':('Originals','empty_fragment_acceptance_rejected'),
'inconsistent-Sim-funds':('Families','mismatched_funds'), 'inconsistent-Sim-ledger':('Families','mismatched_self_ledger','mismatched_external_ledger'),
'inconsistent-Sim-oracle':('Families','mismatched_oracle'), 'resource-bound':('MemoryControls','near_end_state','near_end_allocator','near_end_allocation_rejected'),
'false-loop-invariant':('Calculus','false_annotation_run','false_annotation_rule','false_annotation_init_rejected'),
'observation-erasure':('MemoryControls','allocated_erasure_countercontrol'), 'callback-success':('Callbacks','callback_program_resume'),
'callback-revert':('Callbacks','callback_program_revert'), 'noCallback-policy':('Callbacks','noCallback_excludes_resume','callback_program_noCallback'),
'cleanTail':('TailSensitive','tail_clean_source','dirty_tail_reachable','tail_dirty_source','tail_premise_cannot_be_erased')}
for row in d['controls']:mark(row,*controls[row['name']])
if not any(f['family']=='ExecF' for f in d['constructor_families']):
 text=(root/'Solidity/Semantics/Callback.lean').read_text();body=text[text.index('inductive ExecF '):];body=body[:body.index('\nend Solidity')]
 d['constructor_families'].append({'family':'ExecF','source':'Solidity/Semantics/Callback.lean','constructors':[{'name':n,'status':'open'} for n in re.findall(r'^  \| (\w+)',body,re.M)]})
for f in d['constructor_families']:
 text=(root/f['source']).read_text(); start=text.index('inductive '+f['family']+' ')
 tail=text[start:]; end=re.search(r'\n(?:(?:private|protected|noncomputable|partial) )*(?:inductive|def|theorem|abbrev|end|namespace|section|mutual)\b',tail)
 body=tail[:end.start()] if end else tail; matches=list(re.finditer(r'^  \| (\w+)',body,re.M))
 f['declaration_context']=body[:matches[0].start()].rstrip(); f['declaration_start_line']=text[:start].count('\n')+1
 for i,(row,m) in enumerate(zip(f['constructors'],matches)):
  assert row['name']==m[1]
  clause=body[m.start():matches[i+1].start() if i+1<len(matches) else len(body)].rstrip()
  row.update(source_line=f['declaration_start_line']+body[:m.start()].count('\n'),clause_source=clause,clause_sha256=hashlib.sha256(clause.encode()).hexdigest())
  if f['family']=='Stmt':
   row['syntactic_witnesses']=ws('Families','every_rule_inhabited')
   row['finding']='Semantic antecedent coverage remains open for this exact typed statement clause; the generic state/Rule/Premise.Sound theorem supplies syntactic data and a soundness implication, not truth of its Premise.fml. See source clause and premise coverage ledger.'
  if f['family']=='Stmt' and row['name']=='assert':mark(row,'Calculus','assertion_rule_semantics')
  elif f['family']=='Prog':mark(row,'Calculus','assertion_runs')
  elif f['family']=='Proves' and row['name'] in {'check','closeTrue','closeHolds'}:mark(row,'Calculus','assertion_derivation')
  elif f['family']=='Proves' and row['name']=='updIntro':mark(row,'Callbacks','payment_derivation')
  elif f['family']=='ProvesC' and row['name'] in {'plain','callback'}:mark(row,'Callbacks','payment_derivation')
  elif f['family']=='ExecF':
   mark(row,'CallbackFrames',{'nil':'callback_nil_frame','seq':'callback_seq_frame','seqHalt':'callback_halt_frame','seqViolated':'callback_violated_frame','pop':'callback_pop_frame','drop':'callback_drop_frame'}[row['name']])
  elif f['family']=='Stmt' and row['name'] in {'assignLocal','declLocal','require','revert'}:
   mark(row,'ScalarPremises',{'assignLocal':'flag_rule_application','declLocal':'flag_binding_application','require':'flag_split_application','revert':'revert_rule_application'}[row['name']])
  elif f['family']=='Premise' and row['name'] in {'update','bind','split','done'}:
   mark(row,'ScalarPremises',{'update':'flag_update_antecedent','bind':'flag_binding_antecedent','split':'flag_split_antecedent','done':'revert_done_true'}[row['name']])
  elif f['family']=='ExecP':
   names={'nil':['callback_program_resume'],'cons':['callback_program_resume'],'halt':['callback_program_revert'],'violated':['callback_program_violation']}
   if row['name'] in names:mark(row,'Callbacks',*names[row['name']])
  elif f['family']=='ExecS' and row['name'] in {'det','transferHalt','transferResume','transferViolated'}:
   mark(row,'Callbacks',{'det':'noCallback_transfer','transferHalt':'callback_revert','transferResume':'callback_resume','transferViolated':'callback_violation'}[row['name']])
  elif f['family']=='Premise' and row['name']=='check':mark(row,'Calculus','assertion_rule_semantics')
d['signature_context']='Exact source signatures and constructor clauses are bound to the pinned base; expanded kernel reports are in Signatures.lean. Local witnesses/pins and semantic constructor dispositions have separate gates.'
for family in d['constructor_families']:
 for row in family['constructors']:
  if row['status'] in {'open','durable-open'}:
   row.pop('witness_scope',None)
   row['status']='durable-open'
   row['finding_id']='H28-'+family['family'].upper()+'-'+row['name']
  else: row['witness_scope']='Constructed instance/family of this exact constructor; residual parameter/dispatch cases remain explicit in the source-bound analysis.'
d['acceptance']='incomplete'
p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
print('ledger refreshed; open semantic constructor dispositions preserved')
