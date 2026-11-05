#!/usr/bin/env python3
"""Source-bound remaining semantic obligations, not exclusions or theorem failures."""
import fcntl,hashlib,json,pathlib
here=pathlib.Path(__file__).resolve().parent
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
d=json.loads((here/'inventory.json').read_text())
from importlib.machinery import SourceFileLoader
statement=SourceFileLoader('h28statements',str(here/'statement-findings.py')).load_module().analyses(here.parents[2])
premise={
'update':'A true U-after-run antecedent at a landing state.',
'updates':'Both updates with a typed intermediate state and true continuation.',
'unfold':'Executable replacement plus actual scope-pop Ext.',
'bind':'Replacement execution valid for EVERY intrinsic initially bound value, plus one concrete chosen value and observed result.',
'split':'Concrete condition/branch agreement and separate reachable feasible guards.',
'done':'True branch must be distinguished from done(false), whose antecedent is impossible by done_false_antecedent_rejected.',
'branches':'Nonempty typed branch list and reachable branch/decoded locals.',
'cases':'Concrete formula/update alternatives for success/refusal; jointly empty lists are rejected by empty_cases_guard_rejected.',
'inv':'True entry invariant with preservation and exit use; existing false-entry controls are negative only.',
'inline':'Actual body and Thin return-frame execution.',
'guardedUpdates':'Nonzero update success and zero-divisor revert as separate feasible cases.',
'allocBranches':'Nonempty goals and reached Q, guarded body for EVERY fresh typed MObj, plus one actual constructed object and binding observation.'}
proves={
'intro':'A continuation derivation under H.pre a with a satisfiable if claimed live.',
'notLeft':'Intentional contradictory branch: proved X versus additionally assumed not X; no positive arbitrary consequent claimed.',
'hideLeft':'An existing proof of phi independent of the added antecedent.',
'andIntro':'Both conjunct derivations in the same inhabited context.',
'allIntro':'A derivation under an actual primitive binder and witness value.',
'updIntro':'An actual landing update and continuation derivation.',
'bindIntro':'Continuation valid for EVERY intrinsic bound value, plus one concrete chosen value to show its domain inhabited.',
'allocIntro':'Continuation valid for EVERY fresh typed MObj, plus one actual constructed object witnessing the domain.',
'empty':'An inhabited frame sequence and derivation of its exit.',
'closeFalse':'False cannot hold in a live empty context (false_invariant_entry_rejected); contradictory contexts are closure only.',
'merge':'Both liftBinds?=some and seqPar=some, with actual pre/post contexts and derivations.',
'updRw':'Actual EvalRefines and rewritten continuation derivation.',
'rewrite':'Actual Theq and rewritten context/formula derivation.'}
provesc={
'closeFalse':'Intentional contradiction closure, not arbitrary true execution; callback_false_derivation_rejected excludes nil false.',
'notLeft':proves['notLeft'], 'intro':proves['intro'], 'hideLeft':proves['hideLeft'], 'allIntro':proves['allIntro'],
'havocIntro':'A continuation across actual storage havoc.', 'growIntro':'A continuation across actual typed heap growth.',
'updIntro':proves['updIntro'], 'bindIntro':proves['bindIntro'],
'update':'Rule d, callsBack=false and update continuation.',
'updates':'Rule d, forksIn=false and both update continuations.',
'guardedUpdates':'Rule d, forksIn=false and guarded continuations.',
'unfold':'Rule d, s.forksIn pay=false, replacement P.callsBack pay=false and body continuation.',
'bind':'Rule d, s.forksIn pay=false, replacement P.callsBack pay=false and continuation for EVERY intrinsic bound value.',
'capture':'Actual Rule d, CapturesAs and captured continuation.',
'unfoldReceiver':'Exact double-alias capture Rule and continuation.',
'split':'Rule and both reachable guarded continuations.', 'empty':proves['empty'],
'done':'Rule, forksIn=false and b-branch proof; done(false) cannot have a live antecedent.',
'assert':'True condition and continuation.',
'loopExit':'Actual false-condition capture and unwind-zero obligations.',
'invBox':'Body frame, true entry invariant, preservation and use case.',
'sendDet':'pay=false with actual deterministic success/refusal updates.',
'block':'Actual callback body execution with scope drop.',
'callNone':'Actual argument declarations and callee body.',
'callRets':'Actual argument declarations, callee body and return-variable transfer.',
'callVal':'Actual argument declarations, body and primitive return transfer.',
'callStorage':'Actual argument declarations/body and storage-alias return transfer; the API permits none. A live returned alias is an additional observation target, not an added premise.',
'callMem':'Actual argument declarations/body and default memory-object allocation with hd/hm (defaultOkS/mapFree); query the actual returned object rather than assuming a pointer.',
'transferD':'pay=true, guarded-diamond normality and actual payment continuation.',
'transferDetD':'pay=false, guarded-diamond normality and actual payment continuation.',
'send':'CallbackTaclet, invariant exit, resumed success and refusal branches.',
'sendD':'CallbackTaclet, invariant exit, resumed success, refusal and fml goals.',
'sendDetD':'pay=false, nonnegative amount and both deterministic alternatives.',
'tryCall':'Nonempty CallbackTaclet branches, invariant exit, success and caught branches.',
'trySelf':'LeanTaclet self branch, actual address choices, nonself guarded success and catches.',
'recCall':'Independently proved semantic recContract/recValid and every goals derivation; no assumed desired conclusion.'}
execs={
'sendHalt':'Inhabited boolean target Idx and actual send halt, with pay||full=true.',
'sendFailed':'Inhabited boolean target Idx and successful TRun.transfer premise, but caller state sigma is returned uncharged with false flag, with pay||full=true.',
'sendRefused':'Inhabited boolean target Idx and actual refusal send, with pay||full=true.',
'sendViolated':'Inhabited boolean target Idx and actual invariant-exit violation, with pay||full=true.',
'sendResume':'Inhabited boolean target Idx and actual resumed invariant state, with pay||full=true.',
'iteHalt':'Actual condition evaluation error; nonrevert errors excluded by expression_nonrevert_halt_rejected.',
'iteThen':'Actual true condition and selected ExecP.', 'iteElse':'Actual false condition and selected ExecP.',
'callArgs':'Actual evaluated-argument error.', 'callBody':'Actual argument TEnv and callee-frame ExecP.',
'callRec':'Actual underlying call.', 'callReceiver':'Actual getter call and receiver operation.',
'callReceiverPush':'Successful getter returning some reference and deferred ExecP.',
'callReceiverPushUnset':'Successful getter returning no reference.',
'callReceiverPushHalt':'Actual halted getter.', 'callReceiverPushViolated':'Actual violated getter.',
'tryRevert':'Fully typed intrinsic try statement; unconditional callback overapproximation is not deterministic source revert.',
'tryDecode':'Actual failed return-binder decode.',
'tryViolated':'Entry not J; incompatible with additionally requiring J at that same entry. No global emptiness claimed.',
'tryOk':'Entry/resume invariant, successful decode/ok body, guarded nonself address.',
'tryError':'Nonself address condition and actual error body ExecP.',
'tryPanic':'Nonself address condition, decoded panic code and actual panic body ExecP.',
'tryOther':'Nonself address condition and actual other-catch body ExecP.',
'trySelfOk':'Nonzero self address, successful callee and ok body.',
'trySelfHalt':'Actual exhausted/diverging callee and non-revert/non-panic exclusions.',
'trySelfError':'Actual revertWith data and error body.',
'trySelfOther':'Actual revert/revertWith and other-catch body.',
'trySelfPanic':'Actual panic or correctly decoded panic-data/code-bound body.',
'trySelfViolated':'Actual violated callee.',
'loopHalt':'callsBack body=true and actual condition error.',
'loopExit':'callsBack body=true and actual false condition.',
'loopIter':'callsBack body=true, true condition, successful body and recursive execution.',
'loopStop':'callsBack body=true, true condition and non-ok body.',
'loopDiverge':'callsBack body=true; deliberate callback overapproximation does not prove deterministic source divergence.',
'block':'callsBack body=true and actual body.',
'catchDataHalt':'Callback-bearing clause and e not panic; this overapproximation requires no actual callee-halt derivation.',
'catchDataBody':'Callback-bearing clause, successful litBytes allocation and actual body ExecP.'}
rows=[]
for f in d['constructor_families']:
 for r in f['constructors']:
  if r['status']=='witnessed':continue
  family=f['family']; name=r['name']; maps={'Premise':premise,'Proves':proves,'ProvesC':provesc,'ExecS':execs}
  requirement=maps.get(family,{}).get(name)
  if requirement is None and family in ['Proves','ProvesC'] and name in premise:
   requirement='Exact step-equality Rule d and all continuation derivations/admission, jointly with: '+premise[name]
  if requirement is None and family=='Stmt':
   requirement=statement[name]['missing_constructive_obligation']
  if requirement is None and family=='Prog':
   requirement='A program semantic witness is present in assertion_runs/payment executions, but this row still needs an explicit constructor-level disposition rather than only a containing run.'
  if requirement is None: requirement='Exact constructor continuation/guard obligations shown in the complete source clause; tactic-generated proof term trace has not been extracted and must not be inferred from tactic success alone.'
  rows.append({'dispatch_analysis':statement[name] if family=='Stmt' else None,'id':'H28-'+family.upper()+'-'+name,'status':'durable-open','theorem_falsity':False,'source':f['source'],'line':r['source_line'],'clause_sha256':r['clause_sha256'],'missing_constructive_obligation':requirement,'interpretation':'Coverage finding, not theorem falsity, an exclusion, a new premise, or authorization for producer edits.'})
(here/'open-premises.json').write_text(json.dumps({'status':'durable constructive-coverage findings; not theorem falsity or whole-goal acceptance','findings':rows},indent=2,ensure_ascii=False)+'\n')
print(len(rows),'open exact-clause semantic obligations retained')
