import Solidity.Yul.World.CreditEnvironment
import Solidity.Yul.World.PhysicalCompletionChecks

namespace Solidity.Yul.World.CallerFrameChecks
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.Views.Controls
open Solidity.Yul.World.PhysicalCompletion

def receiver : Roadmap.Address := ⟨64,by decide⟩
def owner : Roadmap.Address := ⟨48,by decide⟩
def sender : Roadmap.Address := ⟨49,by decide⟩
def target : Roadmap.Address := ⟨32,by decide⟩
def locals : Source.Locals packedTypedEnv.layout [.bytes .memory] := .cons (.memRef rfl 0) .nil

def caller : Source.EMState packedTypedEnv [.bytes .memory] :=
  ⟨locals,{PhysicalCompletionChecks.caller.2 with
    ex:=PhysicalCompletionChecks.caller.2.ex.apply (.account receiver (fun a=>{a with balance:=23,nonce:=2,code:=some 0})),
    events:=[.credit receiver 2],logs:=[(owner,[0x70])],fnLocals:=⟨[.bytes .memory],locals⟩}⟩
def residual := PhysicalCompletionChecks.prefixResidual
def encoding := PhysicalCompletionChecks.prefixEncoding

def log : Log := ⟨owner,⟨1,by decide⟩,#v[31],[0x70]⟩
def callerTrace : List Observation := [.event (.credit receiver 2),.log log]
def observed : ObservedEffects packedTypedEnv.layout packedTypedEnv.lay packedTypedEnv.lay :=
  ⟨⟨caller.2.ex,committedLogs callerTrace,[9,8,7,6]⟩,callerTrace,rfl⟩
def parent := caller.2.ex.enter owner sender 0 [] false

def suffix (out : Outcome) : List Observation :=
  [.event (.call target 0 [17,34,51,68] false),.event (.credit receiver 7),.event (.answer out none)]
def events (out : Outcome) : List Roadmap.Event :=
  caller.2.events++[.call target 0 [17,34,51,68] false,.credit receiver 7,.answer out none]

def credited : Source.ExecState packedTypedEnv.layout packedTypedEnv.lay packedTypedEnv.lay :=
  caller.2.ex.apply (.account receiver (fun a=>a.withBalance 30))

def after (out : Outcome) : Source.EMState packedTypedEnv [.bytes .memory] :=
  ⟨locals,{caller.2 with events:=events out,ex:=match out with | .success _=>credited | .revert _=>caller.2.ex}⟩
def result (out : Outcome) : Result packedTypedEnv [.bytes .memory] :=
  (⟨⟨after out,residual⟩,encoding⟩,
    ⟨⟨(after out).2.ex,committedLogs (callerTrace++suffix out),returnData out⟩,callerTrace++suffix out,rfl⟩)

theorem nontrivial_entry : caller.2.ex.journal.length=2 ∧ residual.journal.length=1 ∧ encoding.journal.length=1 ∧
    caller.2.heap.get 0=some ⟨.bytes .memory,.bytes [17,34,51,68]⟩ ∧
    caller.1.get .here = (.memRef rfl 0 : Source.Val packedTypedEnv.layout (.bytes .memory)) ∧ caller.2.logs≠[] := ⟨rfl,rfl,rfl,rfl,rfl,by decide⟩

theorem caller_memOK : Source.MemOK packedTypedEnv PhysicalCompletionChecks.heap.ty caller := by
  have ok := PhysicalCompletionChecks.caller_memOK
  exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,⟨⟨.bytes .memory,rfl,rfl⟩,trivial⟩⟩,ok.2.1,ok.2.2⟩

/-- Actual Source.callAddr call/credit/answer, including its own revert.
No operation list or supplied source execution equality is an input. -/
theorem actual_source_run (G : Glob packedTypedEnv) (out : Outcome) :
    (Source.callAddr (CreditEnvironment.creditGlob G out)
      {this:=owner,sender:=owner,value:=0,static:=false,contract:="EnvironmentCredit",checked:=true,depth:=0,cd:=[]} 3 target 0 [17,34,51,68] false).run
      (Source.L0 packedTypedEnv,caller.2) =
      (.ok out,(Source.L0 packedTypedEnv,(after out).2)) := by
  cases out with
  | success data => rfl
  | revert data =>
    change ((Except.ok (Outcome.revert data) : Except Halt Outcome),
      (Source.L0 packedTypedEnv,{caller.2 with ex:=credited.undo,events:=events (.revert data)})) = _
    rw [show credited.undo=caller.2.ex from Source.ExecState.undo_apply _ _]
    rfl

theorem actual_invoke (G : Glob packedTypedEnv) (out : Outcome) :
    CreditEnvironment.callerInvoke G out observed
      (enter caller residual parent .call target 0 [17,34,51,68]) .call target 10000 [17,34,51,68]
      ⟨⟨caller,residual⟩,encoding⟩ = some ((.ok out,⟨⟨after out,residual⟩,encoding⟩),suffix out) := by
  have ran : CreditEnvironment.invoke G out observed
      (enter caller residual parent .call target 0 [17,34,51,68]) .call target 10000 [17,34,51,68]
      ⟨⟨⟨Source.L0 packedTypedEnv,caller.2⟩,residual⟩,encoding⟩ =
      some ((.ok out,⟨⟨⟨Source.L0 packedTypedEnv,(after out).2⟩,residual⟩,encoding⟩),suffix out) := by
    let sourceRun := (Source.callAddr (CreditEnvironment.creditGlob G out)
      {this:=owner,sender:=owner,value:=0,static:=false,contract:="EnvironmentCredit",checked:=true,depth:=0,cd:=[]} 3 target 0 [17,34,51,68] false).run
      (Source.L0 packedTypedEnv,caller.2)
    change some ((sourceRun.1,(⟨⟨sourceRun.2,residual⟩,encoding⟩ : Carrier packedTypedEnv [])),
      (sourceRun.2.2.events.drop caller.2.events.length).map Observation.event) = _
    have actual : sourceRun=(.ok out,(Source.L0 packedTypedEnv,(after out).2)) := actual_source_run G out
    rw [actual]
    rfl

  exact CallerFrame.liftInvoke_exact (CreditEnvironment.invoke G out) observed
    (enter caller residual parent .call target 0 [17,34,51,68]) .call target 10000 [17,34,51,68]
    ⟨⟨caller,residual⟩,encoding⟩ (.ok out) ⟨⟨⟨Source.L0 packedTypedEnv,(after out).2⟩,residual⟩,encoding⟩ (suffix out) ran

theorem actual_call (G : Glob packedTypedEnv) (out : Outcome) :
    call (CreditEnvironment.callerInvoke G out) caller residual encoding observed rfl PhysicalCompletionChecks.memory parent .call
      target 10000 0 160 4 =
      some (.ok out,finish caller encoding observed (enter caller residual parent .call target 0 [17,34,51,68])
        ⟨⟨after out,residual⟩,encoding⟩ (suffix out) out) := by
  apply call_normal_rule (CreditEnvironment.callerInvoke G out) caller residual encoding observed rfl PhysicalCompletionChecks.memory parent .call
    target 10000 0 160 4 [17,34,51,68] ⟨⟨after out,residual⟩,encoding⟩ (suffix out) out rfl _ (actual_invoke G out)
  rw [PhysicalHeapPort.load_view _ _ _ (by decide)]
  exact congrArg some (bytesObject_payload_list _ _ _ 128)

theorem actual_completion (out : Outcome) :
    finish caller encoding observed (enter caller residual parent .call target 0 [17,34,51,68])
      ⟨⟨after out,residual⟩,encoding⟩ (suffix out) out = result out := by
  cases out <;> rfl

theorem source_composition (G : Glob packedTypedEnv) (out : Outcome) :
    call (CreditEnvironment.callerInvoke G out) caller residual encoding observed rfl PhysicalCompletionChecks.memory parent .call
      target 10000 0 160 4 = some (.ok out,result out) := by
  rw [actual_call G out,actual_completion out]

/-- All caller frame fields, journals and complete ordered trace, not just
an event projection. Events and the full last-frame buffer are observable. -/
theorem caller_frame (out : Outcome) :
    (result out).1.1.1.1=caller.1 ∧ (result out).1.1.1.2.heap=caller.2.heap ∧
    (result out).1.1.1.2.fnLocals=caller.2.fnLocals ∧ (result out).1.1.1.2.logs=caller.2.logs ∧
    (result out).1.1.1.2.events=events out ∧ (result out).1.1.2=residual ∧ (result out).1.2=encoding ∧
    (result out).2.trace=callerTrace++suffix out ∧ (result out).2.effects.returndata=returnData out := by
  cases out <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem success_credit : ((result (.success [0x99])).1.1.1.2.ex.world.accounts receiver).balance=30 ∧
    (result (.success [0x99])).1.1.1.2.ex.journal.length=3 := ⟨rfl,rfl⟩
theorem revert_credit : (result (.revert [0xde])).1.1.1.2.ex=caller.2.ex ∧
    ((result (.revert [0xde])).1.1.1.2.ex.world.accounts receiver).balance=23 := ⟨rfl,rfl⟩

theorem owner_MemOK (out : Outcome) : Source.MemOK packedTypedEnv PhysicalCompletionChecks.heap.ty (result out).1.1.1 := by
  have ok := caller_memOK
  cases out <;> exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2.1,ok.2.2⟩

theorem output_copy : copyOutput (result (.revert [0xde,0xad,0xbe])) rfl PhysicalCompletionChecks.placement 0 false [17,34,51,68] rfl PhysicalCompletionChecks.memory 1 2 =
    (result (.revert [0xde,0xad,0xbe]),some ((Solidity.Backend.Environment.writeBytes PhysicalCompletionChecks.memory 161 [0xde,0xad],
      withSourceHeap (after (.revert [0xde,0xad,0xbe])) (PhysicalCompletionChecks.heap.write 0 (.bytes [17,0xde,0xad,68]) rfl)),
      (residual,encoding),(result (.revert [0xde,0xad,0xbe])).2)) :=
  copyOutput_exact (result (.revert [0xde,0xad,0xbe])) rfl PhysicalCompletionChecks.placement 0 false [17,34,51,68] rfl PhysicalCompletionChecks.memory 1 2
    (by decide) (congrArg Fin.val (bytesObject_header _ _ _ 128)) (bytesObject_payload_list _ _ _ 128)

theorem nonempty_function_frame : caller.2.fnLocals.1=[.bytes .memory] ∧ receiver≠owner ∧ owner≠sender ∧ target≠receiver :=
  ⟨rfl,by decide,by decide,by decide⟩

theorem alias_read (out : Outcome) :
    (Source.bytesOfRV (E:=packedTypedEnv) {this:=owner,sender:=sender,value:=0,static:=false,contract:="Finite",checked:=true,depth:=0,cd:=[]} 1
      (.val ((result out).1.1.1.1.get .here))).run (result out).1.1.1 =
      (.ok [17,34,51,68],(result out).1.1.1) := by
  cases out <;> rfl

theorem persistent_word_unchanged (out : Outcome) :
    reencodePersistentSlot (representedBanks packedTypedRegistry false encoding)
      ⟨(result out).2.effects.execution,residual⟩ account 7=some dirtyBoolRaw := by
  cases out <;> exact dirty_bool_exact_raw

theorem account_metadata (out : Outcome) :
    ((result out).1.1.1.2.ex.world.accounts receiver).nonce=2 ∧
    ((result out).1.1.1.2.ex.world.accounts receiver).code=some 0 ∧
    ((result out).1.1.1.2.ex.world.accounts receiver).storage=(caller.2.ex.world.accounts receiver).storage ∧
    (result out).1.1.1.2.ex.transient=caller.2.ex.transient := by
  cases out <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem bad_source_zero : copyAfter (result (.revert [0xde,0xad,0xbe])) rfl PhysicalCompletionChecks.placement
    0 false [17,34,51,68] rfl PhysicalCompletionChecks.memory 4 4 0 = (result (.revert [0xde,0xad,0xbe]),none) :=
  copyAfter_bad_source _ _ _ _ _ _ _ _ _ _ _ (by decide)

theorem exact_buffer_and_tail : (result (.revert [0xde,0xad,0xbe])).2.effects.returndata=[0xde,0xad,0xbe] ∧
    returnWindow (result (.revert [0xde,0xad,0xbe])).2.effects.returndata 3 0=some [] ∧
    (result (.revert [0xde,0xad,0xbe])).2.trace≠callerTrace++
      [.event (.call target 0 [17,34,51,68] false),.event (.answer (.revert [0xde,0xad,0xbe]) none)] := by decide

/-- Actual source instance boundary after a dispatch attempt: heap is cleared,
then restored before timeout propagates. This is not an EVM failure verdict. -/
def instancePrefix (G : Glob packedTypedEnv) :=
  let run := CallerFrame.runInstance (CreditEnvironment.creditGlob G (.success [])) caller 0
    receiver owner 0 [17,34,51,68] false "Finite" 1
  (run.1.map Prod.fst,(⟨⟨run.2,residual⟩,encoding⟩ : Carrier packedTypedEnv [.bytes .memory]))

theorem actual_instance_timeout (G : Glob packedTypedEnv) : instancePrefix G=(.error .timeout,⟨⟨caller,residual⟩,encoding⟩) := rfl

theorem timeout_pending_full (G : Glob packedTypedEnv) :
    completeReturned caller encoding observed (enter caller residual parent .call receiver 0 [17,34,51,68])
      (instancePrefix G,[]) = (.error .timeout,(⟨⟨caller,residual⟩,encoding⟩,observed)) := rfl

theorem enclosing_revert :
    finish caller encoding observed (enter caller residual parent .call target 0 [17,34,51,68])
      (result (.success [0x99,0x88,0x77])).1 (suffix (.success [0x99,0x88,0x77])) (.revert [0xee]) =
      (⟨⟨⟨locals,{caller.2 with events:=events (.success [0x99,0x88,0x77])}⟩,residual⟩,encoding⟩,
        ⟨⟨caller.2.ex,committedLogs (callerTrace++suffix (.success [0x99,0x88,0x77])),[0xee]⟩,
          callerTrace++suffix (.success [0x99,0x88,0x77]),rfl⟩) := by
  change ((⟨⟨⟨locals,{caller.2 with ex:=credited.undo,events:=events (.success [0x99,0x88,0x77])}⟩,residual⟩,encoding⟩,
    ⟨⟨credited.undo,committedLogs (callerTrace++suffix (.success [0x99,0x88,0x77])),[0xee]⟩,
      callerTrace++suffix (.success [0x99,0x88,0x77]),rfl⟩) : Result packedTypedEnv [.bytes .memory]) = _
  rw [show credited.undo=caller.2.ex from Source.ExecState.undo_apply _ _]

theorem static_refused (G : Glob packedTypedEnv) out :
    CreditEnvironment.callerInvoke G out observed (enter caller residual parent .staticcall target 0 [17,34,51,68])
      .staticcall target 10000 [17,34,51,68] ⟨⟨caller,residual⟩,encoding⟩=none := rfl

theorem precompile_refused (G : Glob packedTypedEnv) out :
    CreditEnvironment.callerInvoke G out observed (enter caller residual parent .call ⟨2,by decide⟩ 0 [17,34,51,68])
      .call ⟨2,by decide⟩ 10000 [17,34,51,68] ⟨⟨caller,residual⟩,encoding⟩=none := rfl

theorem receiver_registered (G : Glob packedTypedEnv) out :
    (caller.2.ex.world.accounts receiver).code=some 0 ∧
    (CreditEnvironment.creditGlob G out).contractAt 0=some "Finite" ∧
    ¬Roadmap.Address.Precompile receiver := by
  refine ⟨rfl,rfl,?_⟩
  intro h
  change false=true at h
  cases h

def unregistered : Carrier packedTypedEnv [.bytes .memory] :=
  ⟨⟨⟨caller.1,{caller.2 with ex:=caller.2.ex.apply (.account receiver (fun a=>{a with code:=none}))}⟩,residual⟩,encoding⟩
def overflow : Carrier packedTypedEnv [.bytes .memory] :=
  ⟨⟨⟨caller.1,{caller.2 with ex:=caller.2.ex.apply (.account receiver
    (fun a=>a.withBalance ⟨2^256-1,by decide⟩))}⟩,residual⟩,encoding⟩

def withExecution (c : Carrier packedTypedEnv [.bytes .memory]) : ObservedEffects packedTypedEnv.layout packedTypedEnv.lay packedTypedEnv.lay :=
  ⟨⟨c.1.1.2.ex,observed.effects.logs,observed.effects.returndata⟩,observed.trace,observed.logs_eq⟩

theorem registration_refusal (G : Glob packedTypedEnv) out :
    CreditEnvironment.callerInvoke G out (withExecution unregistered)
      (enter unregistered.1.1 unregistered.1.2 parent .call target 0 [17,34,51,68])
      .call target 10000 [17,34,51,68] unregistered=none := rfl

theorem range_refusal (G : Glob packedTypedEnv) out :
    CreditEnvironment.callerInvoke G out (withExecution overflow)
      (enter overflow.1.1 overflow.1.2 parent .call target 0 [17,34,51,68])
      .call target 10000 [17,34,51,68] overflow=none := rfl

theorem wrong_context_refusal (G : Glob packedTypedEnv) out :
    CreditEnvironment.callerInvoke G out observed (enter caller residual parent .call ⟨33,by decide⟩ 0 [17,34,51,68])
      .call target 10000 [17,34,51,68] ⟨⟨caller,residual⟩,encoding⟩=none := rfl

def partialSuffix : List Observation := [.event (.call target 0 [17,34,51,68] false),.event (.credit receiver 7)]
def partialState : Source.EMState packedTypedEnv [.bytes .memory] :=
  ⟨locals,{caller.2 with ex:=credited,events:=caller.2.events++[.call target 0 [17,34,51,68] false,.credit receiver 7]}⟩
def partialResult : Result packedTypedEnv [.bytes .memory] := pending observed ⟨⟨partialState,residual⟩,encoding⟩ partialSuffix

theorem source_credit_timeout (G : Glob packedTypedEnv) out :
    (Source.callAddr (CreditEnvironment.creditGlob G out) {this:=owner,sender:=owner,value:=0,static:=false,contract:="EnvironmentCredit",checked:=true,depth:=0,cd:=[]}
      2 target 0 [17,34,51,68] false).run (Source.L0 packedTypedEnv,caller.2) =
      (.error .timeout,(Source.L0 packedTypedEnv,partialState.2)) := rfl

theorem prefix_invoke_actual (G : Glob packedTypedEnv) out :
    CallerFrame.liftInvoke (CreditEnvironment.prefixInvoke G out) observed
      (enter caller residual parent .call target 0 [17,34,51,68]) .call target 10000 [17,34,51,68]
      ⟨⟨caller,residual⟩,encoding⟩ = some ((.error .timeout,⟨⟨partialState,residual⟩,encoding⟩),partialSuffix) := rfl

theorem prefix_call_actual (G : Glob packedTypedEnv) out :
    call (CallerFrame.liftInvoke (CreditEnvironment.prefixInvoke G out)) caller residual encoding observed rfl
      PhysicalCompletionChecks.memory parent .call target 10000 0 160 4 = some (.error .timeout,partialResult) := by
  have loaded : PhysicalHeapPort.port.load PhysicalCompletionChecks.memory 160 4=some [17,34,51,68] := by
    rw [PhysicalHeapPort.load_view _ _ _ (by decide)]
    exact congrArg some (bytesObject_payload_list _ _ _ 128)
  exact call_exact (CallerFrame.liftInvoke (CreditEnvironment.prefixInvoke G out)) caller residual encoding observed rfl
    PhysicalCompletionChecks.memory parent .call target 10000 0 160 4 [17,34,51,68] _ rfl loaded (prefix_invoke_actual G out)

theorem dirty_timeout_full : partialResult.1=⟨⟨partialState,residual⟩,encoding⟩ ∧
    partialResult.1.1.1.2.ex.journal.length=3 ∧
    (partialResult.1.1.1.2.ex.world.accounts receiver).balance=30 ∧
    partialResult.2.trace=callerTrace++partialSuffix ∧ partialResult.2.effects.returndata=[9,8,7,6] ∧
    partialResult.1.1.1.1=caller.1 ∧ partialResult.1.1.1.2.heap=caller.2.heap ∧
    partialResult.1.1.1.2.fnLocals=caller.2.fnLocals ∧ partialResult.1.1.1.2.logs=caller.2.logs :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem completed_extends_pending (out : Outcome) : partialResult.2.trace <+: (result out).2.trace :=
  List.prefix_append (callerTrace++partialSuffix) [.event (.answer out none)]

def copiedState := withSourceHeap (after (.revert [0xde,0xad,0xbe]))
  (PhysicalCompletionChecks.heap.write 0 (.bytes [17,0xde,0xad,68]) rfl)

theorem exact_state_copy : HeapWindow.copyStateWindow (result (.revert [0xde,0xad,0xbe])).2.effects
    (result (.revert [0xde,0xad,0xbe])).1.1.1 PhysicalCompletionChecks.placement 0 false [17,34,51,68] rfl
    PhysicalCompletionChecks.memory 1 0 2 =
      some (Solidity.Backend.Environment.writeBytes PhysicalCompletionChecks.memory 161 [0xde,0xad],copiedState) :=
  HeapWindow.copyStateWindow_exact _ _ _ _ _ _ [0xde,0xad] rfl _ 1 0 2 rfl (by decide)
    (congrArg Fin.val (bytesObject_header _ _ _ 128)) (bytesObject_payload_list _ _ _ 128)

theorem copied_owner_MemOK : Source.MemOK packedTypedEnv PhysicalCompletionChecks.heap.ty copiedState :=
  HeapWindow.copyStateWindow_memOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ exact_state_copy (owner_MemOK (.revert [0xde,0xad,0xbe]))

theorem copied_aliases :
    (Source.bytesOfRV (E:=packedTypedEnv) {this:=owner,sender:=sender,value:=0,static:=false,contract:="Finite",checked:=true,depth:=0,cd:=[]} 1
      (.val (copiedState.1.get .here))).run copiedState = (.ok [17,0xde,0xad,68],copiedState) ∧
    (Source.bytesOfRV (E:=packedTypedEnv) {this:=owner,sender:=sender,value:=0,static:=false,contract:="Finite",checked:=true,depth:=0,cd:=[]} 1
      (.val (copiedState.2.fnLocals.2.get .here))).run copiedState = (.ok [17,0xde,0xad,68],copiedState) := ⟨rfl,rfl⟩

end Solidity.Yul.World.CallerFrameChecks
