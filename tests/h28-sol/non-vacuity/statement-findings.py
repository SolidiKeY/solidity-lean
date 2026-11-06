#!/usr/bin/env python3
"""Reviewed exact dispatch/helper identities and missing semantic witnesses.
These are durable coverage findings, never new theorem premises or exclusions.
"""
import hashlib,pathlib,re
DATA={
'assert':('Arms','assertStep','Calculus queries the simple true-condition check with its actual true antecedent. The simple false condition has no true check antecedent; complex conditions still need an actual evaluated Bool, capture temporary scope and assertion/continuation observation. No complex capture witness is claimed.'),
'assign':('Arms','assignStep','Actual root/field/index location and RHS read, or mapFree copy/capture order, with changed destination observation. The uint storage run alone does not establish every selected semantic step antecedent.'),
'rebind':('Arms','rebindStep','Occupied alias Idx, live resolved source or appended reference, and resulting alias observation for the selected update/capture branch.'),
'assignLocal':('Arms','localStep','ScalarPremises queries Bool assignment false/true to true. Numeric/read/binop/short-circuit/ternary operand and capture cases still need their actual Idx, evaluated operands and changed-local observations.'),
'declLocal':('Step','Stmt.step','ScalarPremises queries initialized Bool binding for EVERY initial Bool and observes the assertion. None/default-update and other initializer/type/capture cases remain distinct; they need true premises and overwrite/continuation observations.'),
'declStorage':('Step','Stmt.step','None/unset and some/bind+rebind are distinct. A source path must resolve, and the replacement must be valid for every initially bound alias, with one actual live result. Unset is not a live alias.'),
'opAssign':('Arms','opStep','Accepted operation/numeric type, live target and evaluated operands, nonoverflow/nonzero guards as applicable, and saved result in the selected update/capture branch.'),
'incDec':('Arms','incStep','Actual bounded numeric before/after values and live receiver, retaining the selected increment/decrement and capture cases.'),
'assignIncDec':('Arms','assignIncStep','Actual value-target Idx and numeric operand, with the selected pre/post return value (NEW for pre, OLD for post) and changed cell jointly observed after the parallel update.'),
'assignLocalPush':('Arms','assignLocalPushStep','Actual target Idx and growable primitive array, appended default and saved returned value; distinguish receiver captures.'),
'push':('Arms','pushStep','Live growable array and capacity, actual defaultOkS/typed element or copy source, and final length plus element; distinguish allocation/copy/capture branches.'),
'pop':('Arms','popStep','Actual nonempty array and decremented length, distinguishing mapping-element shrink and captured receiver/index cases.'),
'pushOpAssign':('Arms','pushOpStep','Two actual landings: append then arithmetic/save, with retained length/value. Division/modulo need separate nonzero success and zero-divisor revert-before-append cases.'),
'pushIncDec':('Arms','pushIncStep','Actual pushSlot and arithmetic-save landings, observing appended/incremented value and retained length.'),
'transfer':('Arms','transferStep','Simple box payment-update needs a true semantic antecedent at funded/oracle-matched inputs. Existing payment runs do not instantiate this formula. Simple diamond done(false) is intentional impossibility, not successful coverage.'),
'send':('Arms','sendStep','Actual boolean target, recipient and amount. cases requires BOTH success and refusal updates with corresponding flag/net observations; diamond also requires nonnegative amount. A flag=true-only post would be invalid.'),
'declMem':('Step','Stmt.step','None/default allocation update and some/bind+rebindMem differ. Need actual default/mapFree object and pointer, and true full semantic declaration premise for every initial intrinsic bound pointer; source allocation alone does not establish that premise.'),
'rebindMem':('Arms','rebindMemStep','Occupied pointer Idx, live resolved RHS or actual new/deep-copy object, and resulting pointer/payload observation for the selected branch.'),
'assignFromMem':('Arms','assignFromMemStep','Live source HRef, valid storage destination, actual copied payload and changed storage observation; distinguish source/receiver capture order.'),
'assignMem':('Arms','assignMemStep','Actual typed object and field/index, in-bounds index, evaluated payload and resulting memory observation; preserve all capture order cases.'),
'delete':('Arms','deleteStep','Actual live target with nondefault before/default after storage observation and selected receiver/index captures.'),
'deleteMem':('Arms','deleteMemStep','Actual defaultOkS/mapFree, live root or valid sublocation, and fresh replacement/default payload observation; root allocFresh differs from member/index clearMem.'),
'assignNew':('Arms','assignNewStep','Actual newArrOk, length/capacity and fresh typed object, valid NewLhs receiving the pointer/payload, and unfolded scope pop.'),
'ite':('Arms','iteStep','Concrete conditions selecting separate feasible branches, actual bodies and join certificate or true split semantic antecedent. A joinable sample does not witness split.'),
'require':('Arms','requireStep','ScalarPremises queries both Bool-local guard valuations with a nonempty continuation under the simple split(nil,revert). Complex-condition capture still needs an actual evaluated condition and temporary-scope observation.'),
'revert':('Step','Stmt.step','ScalarPremises queries box done(true) and actual revert. Diamond done(false) has no true antecedent by done_false_antecedent_rejected. A normal source landing is impossible by design, not missing compiler success.'),
'assumeFalse':('Step','Stmt.step','Done(true) accompanies actual source exhausted, not normal success. assumption_exhausts/not_successful/fragment_rejected retain this intentional boundary.'),
'call':('Blocks','callStep','Actual evaluated Args, intrinsic return/body contexts and selected summary/update or capture/unfold/inline shape, with body/frame/result observations. The scalar memoryCalls client contains no call operation.'),
'callRec':('Step','Stmt.step','Actual finite underlying body(), Args and CallRet with frame-return observation. This unfolding shape cannot be witnessed by assuming a recursive correctness conclusion.'),
'callReceiver':('Blocks','callReceiverStep','Actual getter Args/body yielding a live array alias, receiver push/pop result and both alias scope drops.'),
'callReceiverPush':('Blocks','ReceiverValue.step','Actual successful getter alias, deferred prefix execution/value, getter-before-prefix-before-push order and both alias frames.'),
'tryCall':('Blocks','tryStepS','Actual intrinsic ExtCall/Binders/CodeBinder, address/self guards, decoding/catch bodies and each feasible result under box. Diamond done(false) is intentional; no positive diamond antecedent claimed.'),
'loop':('Blocks','loopStep','Selected annotation/condition/body/frame and true entry/preservation/exit; a diamond variant must satisfy decrease. Divergence and false-invariant controls do not supply all annotation cases.'),
'block':('Step','Stmt.step','Actual nonempty body, typed body.ext scope drop and continuation semantic antecedent, including declared locals rather than an empty block.'),
'revertData':('Step','Stmt.step','Actual evaluated bytes/selector with error-data observation for box. Diamond done(false) cannot have a true antecedent; neither mode promises normal source success.'),
'catchData':('Blocks','catchDataStep','Actual address guards/CatchKind/data matching and nonempty reachable goals. allocBranches body must hold for EVERY fresh bytes MObj, plus an actual nonempty bytes object and binding observation; known and unknown-data cases stay distinct.')}
def declaration(text,name):
 m=re.search(r'^(?:(?:private|protected|noncomputable|partial) )*(?:def|abbrev|theorem) '+re.escape(name)+r'(?=[\s{(:])',text,re.M)
 assert m,name
 end=re.search(r'\n(?:(?:private|protected|noncomputable|partial) )*(?:def|abbrev|theorem|namespace|end|section|inductive)\b',text[m.end():])
 stop=m.end()+end.start() if end else len(text)
 return text[m.start():stop].rstrip(),text[:m.start()].count('\n')+1

def analyses(root):
 out={}
 for name,(file,helper,obligation) in DATA.items():
  source='Solidity/Calculus/'+file+'.lean';raw=(root/source).read_bytes();text,line=declaration(raw.decode(),helper)
  out[name]={'source':source,'declaration':helper,'line':line,'text':text,'source_sha256':hashlib.sha256(raw).hexdigest(),'text_sha256':hashlib.sha256(text.encode()).hexdigest(),'missing_constructive_obligation':obligation}
 return out
