import Solidity.Yul.World.PhysicalCall
import Solidity.Yul.World.PhysicalCompletionFrames
import Solidity.Yul.World.PhysicalEnvironmentAnswer
import Solidity.Yul.World.PhysicalPortChecks

namespace Solidity.Yul.World.PhysicalCompletionChecks
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.Views.Controls
open Solidity.Yul.World.PhysicalCompletion

/-- Same actual packed-slot environment, now with a real allocated caller
payload. No cast between the physical producer's two different environments. -/
def heap : Source.Heap packedTypedEnv.layout :=
  (Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [17,34,51,68]⟩).1

def placement : Placement heap where
  address a := 128+a*128
  shape _ := .bytes 4
  free := ⟨256,by decide⟩
  free_start := by decide
  distinct a b _ _ ne := by omega
  typed a τ d found := by
    cases a with
    | zero =>
      change some (⟨.bytes .memory,.bytes [17,34,51,68]⟩ : Σ σ,Source.Data packedTypedEnv.layout σ)=some ⟨τ,d⟩ at found
      cases found
      exact .bytes _
    | succ a =>
      have absent := heap.bounded (a+1) (by change 1 ≤ a+1; omega)
      change heap.cells (a+1)=some ⟨τ,d⟩ at found
      rw [absent] at found
      cases found
  starts _ _ := by omega
  ends a live := by
    have bound : a<1 := by
      apply Nat.lt_of_not_le
      intro hn
      have absent := heap.bounded a (by change 1 ≤ a; omega)
      rw [absent] at live
      cases live
    have zero : a=0 := by omega
    subst a
    decide
  separate a b _ _ ne := by change 128+a*128+64 ≤ 128+b*128 ∨ 128+b*128+64 ≤ 128+a*128; omega

def memory : ByteView := bytesObjectView [17,34,51,68] (by decide)
  (mstore (mstore (fun _=>0xa5) 64 256) 96 0) 128

def caller : Source.EMState packedTypedEnv [] :=
  ⟨.nil,{dirtyBoolRun.1.1.2.2 with heap:=heap,events:=[.credit account 13],logs:=[(account,[0x70])]}⟩
def observed : ObservedEffects packedTypedEnv.layout packedTypedEnv.lay packedTypedEnv.lay :=
  ⟨⟨caller.2.ex,committedLogs Checks.callerTrace,[9,8,7,6]⟩,Checks.callerTrace,rfl⟩
def prefixResidual := dirtyBoolRun.1.2
def prefixEncoding := dirtyBoolRun.2

def prior : List Observation := [.event (.credit account 17),.log Checks.l0]
def suffix : List Observation :=
  [.log Checks.l4,.event (.answer (.success [8]) none),.log Checks.l0,.event (.credit account 19)]

def physical := PhysicalSlotPort.step packedTypedRegistry packedTypedRegistry dirtyBoolThreeRequest prefixEncoding
  (PhysicalPortChecks.delegatedFrame false) dirtyBoolThreePlan caller prefixResidual observed rfl rfl

def frame := companionEnter (⟨caller.2.ex,prefixResidual⟩ : ResidualCompanion packedTypedEnv.layout packedTypedEnv.lay packedTypedEnv.lay complementCarrierOwnership)
  account (PhysicalPortChecks.delegatedFrame false).sender 17 [] false

def successful : Result packedTypedEnv [] :=
  finish caller prefixEncoding observed frame ⟨⟨physical.1.1.1.2,physical.1.1.2⟩,physical.1.2⟩ suffix (.success [0x99,0x88,0x77])
def reverted : Result packedTypedEnv [] :=
  finish caller prefixEncoding observed frame ⟨⟨physical.1.1.1.2,physical.1.1.2⟩,physical.1.2⟩ suffix (.revert [0xde,0xad,0xbe])

theorem actual_success : slot (PhysicalPortChecks.delegatedFrame false) dirtyBoolThreePlan caller prefixResidual
    observed rfl rfl suffix (.success [0x99,0x88,0x77]) = (.ok (.success [0x99,0x88,0x77]),successful) :=
  slot_success _ _ _ _ _ rfl rfl _ _ rfl

theorem actual_revert : reverted =
    (⟨⟨caller,prefixResidual⟩,prefixEncoding⟩,
      ⟨⟨caller.2.ex,committedLogs (rollbackTrace observed.trace suffix),[0xde,0xad,0xbe]⟩,
        rollbackTrace observed.trace suffix,rfl⟩) := by
  have h := slot_revert (PhysicalPortChecks.delegatedFrame false) dirtyBoolThreePlan caller prefixResidual observed rfl rfl suffix [0xde,0xad,0xbe] rfl
  change ((Except.ok (Outcome.revert [0xde,0xad,0xbe]) : Except Halt Outcome),reverted) = _ at h
  exact (Prod.mk.inj h).2

theorem nonempty_three_prefixes : caller.2.ex.journal.length=1 ∧ prefixResidual.journal.length=1 ∧
    prefixEncoding.journal.length=1 ∧ caller.2.events≠[] ∧ caller.2.logs≠[] := by decide

theorem success_full_word :
    reencodePersistentSlot (representedBanks packedTypedRegistry false successful.1.2)
      ⟨successful.2.effects.execution,successful.1.1.2⟩ account 7 = some dirtyBoolThreeRequest.raw :=
  PhysicalSlotPort.persistent_word (PhysicalPortChecks.delegatedFrame false) dirtyBoolThreePlan caller prefixResidual observed rfl rfl rfl rfl
    ((packedSeparationCheck_iff (packedTypedRegistry account)).mp (by decide))

theorem complete_trace : successful.2.trace=observed.trace++suffix ∧
    reverted.2.trace=rollbackTrace observed.trace suffix ∧
    reverted.2.trace≠observed.trace ∧ reverted.2.trace≠observed.trace++suffix := by decide

theorem delegated_owner : (PhysicalPortChecks.delegatedFrame false).this=account ∧
    (PhysicalPortChecks.delegatedFrame false).sender=(⟨account.val+2,by decide⟩ : Roadmap.Address) ∧
    (PhysicalPortChecks.delegatedFrame false).value=17 := ⟨rfl,rfl,rfl⟩

theorem static_no_suffix : slot (PhysicalPortChecks.delegatedFrame true) dirtyBoolThreePlan caller prefixResidual
    observed rfl rfl suffix (.success [99]) =
      (.ok (.revert []),(⟨⟨caller,prefixResidual⟩,prefixEncoding⟩,
        ⟨⟨caller.2.ex,committedLogs observed.trace,[]⟩,observed.trace,rfl⟩)) :=
  slot_static _ _ _ _ _ rfl rfl _ _ rfl

/-- Two actual prepared requests: persistent then transient, each writes the
owned bool byte and residual padding; success keeps journals for enclosing revert. -/
def transientRequest : PackedSlotRequest := ⟨true,account,7,⟨0xabcdef000005,by decide⟩⟩
def transientPrepared := prepareRepresentedSlot packedTypedRegistry packedTypedRegistry transientRequest
  (requestEncoding packedTypedRegistry packedTypedRegistry dirtyBoolThreeRequest prefixEncoding)
theorem transient_ready : transientPrepared.isSome := by decide
def transientPlan := transientPrepared.get transient_ready

theorem enclosing_revert :
    let firstObserved : ObservedEffects packedTypedEnv.layout packedTypedEnv.lay packedTypedEnv.lay :=
      ⟨⟨physical.2.effects.execution,committedLogs (observed.trace++prior),[]⟩,observed.trace++prior,rfl⟩
    let second := PhysicalSlotPort.step packedTypedRegistry packedTypedRegistry transientRequest
      (requestEncoding packedTypedRegistry packedTypedRegistry dirtyBoolThreeRequest prefixEncoding)
      packedStepFrame transientPlan physical.1.1.1.2 physical.1.1.2 firstObserved rfl rfl
    let child := finish physical.1.1.1.2 (requestEncoding packedTypedRegistry packedTypedRegistry dirtyBoolThreeRequest prefixEncoding)
      firstObserved (companionEnter ⟨physical.2.effects.execution,physical.1.1.2⟩
        packedStepFrame.this packedStepFrame.sender packedStepFrame.value [] packedStepFrame.static)
      ⟨⟨second.1.1.1.2,second.1.1.2⟩,second.1.2⟩ suffix (.success [0x44])
    finish caller prefixEncoding observed frame child.1 (prior++suffix) (.revert [0xee]) =
      (⟨⟨caller,prefixResidual⟩,prefixEncoding⟩,
        ⟨⟨caller.2.ex,committedLogs (rollbackTrace observed.trace (prior++suffix)),[0xee]⟩,
          rollbackTrace observed.trace (prior++suffix),rfl⟩) ∧
    child.2.trace=(observed.trace++prior)++suffix :=
  nested_commit_revert (PhysicalPortChecks.delegatedFrame false) packedStepFrame
    dirtyBoolThreePlan caller prefixResidual observed rfl rfl transientRequest transientPlan rfl rfl rfl prior suffix [0x44] [0xee]

/-- Child revert restores storage but caller output bytes still change. Full
returned data is3 bytes while capacity2 touches only the payload's middle2. -/
theorem revert_output : copyOutput reverted (finish_shared _ _ _ _ _ _ _)
    placement 0 false [17,34,51,68] rfl memory 1 2 =
      (reverted,some ((Solidity.Backend.Environment.writeBytes memory 161 [0xde,0xad],
        withSourceHeap caller (heap.write 0 (.bytes [17,0xde,0xad,68]) rfl)),
        (prefixResidual,prefixEncoding),reverted.2)) := by
  simpa only [actual_revert] using copyOutput_exact reverted (finish_shared _ _ _ _ _ _ _) placement 0 false [17,34,51,68] rfl memory 1 2 (by decide)
    (congrArg Fin.val (bytesObject_header _ _ _ 128)) (bytesObject_payload_list _ _ _ 128)

theorem output_tail_unchanged : HeapWindow.splice [17,34,51,68] 1 [0xde,0xad]=[17,0xde,0xad,68] := rfl

theorem bad_source_zero : copyAfter reverted (finish_shared _ _ _ _ _ _ _)
    placement 0 false [17,34,51,68] rfl memory 4 4 0 = (reverted,none) :=
  copyAfter_bad_source _ _ _ _ _ _ _ _ _ _ _ (by decide)

theorem last_buffer_full : reverted.2.effects.returndata=[0xde,0xad,0xbe] ∧
    returnWindow reverted.2.effects.returndata 3 0=some [] ∧ returnWindow reverted.2.effects.returndata 4 0=none := by decide

theorem pending_stuck : finishStep caller prefixEncoding observed frame
    (((.error (.stuck "physical boundary"),physical.1.1.1.2),physical.1.1.2),physical.1.2)
    suffix (.success [99]) =
      (.error (.stuck "physical boundary"),pending observed ⟨⟨physical.1.1.1.2,physical.1.1.2⟩,physical.1.2⟩ suffix) := rfl

theorem pending_timeout : finishStep caller prefixEncoding observed frame
    (((.error .timeout,physical.1.1.1.2),physical.1.1.2),physical.1.2)
    suffix (.revert []) =
      (.error .timeout,(⟨⟨physical.1.1.1.2,physical.1.1.2⟩,physical.1.2⟩,
        ⟨⟨physical.1.1.1.2.2.ex,committedLogs (observed.trace++suffix),observed.effects.returndata⟩,
          observed.trace++suffix,rfl⟩)) := rfl

/-- Source-only counter-control: this interpreter calculation at precompile2
is NOT an allowed environment witness. The new producer rejects that address;
precompile classification remains a source-owner adequacy obligation. -/
theorem source_only_unclassified_call (G : Glob packedTypedEnv) (out : Outcome) :
    (Source.callAddr (answerStrategy G out) packedStepFrame 2 (⟨2,by decide⟩) 0 [0xaa] false).run caller =
      (.ok out,(caller.1,{caller.2 with events:=caller.2.events++
        [.call ⟨2,by decide⟩ 0 [0xaa] false,.answer out none]})) := by
  cases out <;> rfl

theorem caller_memOK : MemOK packedTypedEnv heap.ty caller := by
  have ok : HeapOK (E:=packedTypedEnv) heap := HeapOK.alloc HeapOK.empty (.bytes [17,34,51,68])
  have shaped : HeapShaped (E:=packedTypedEnv) heap := HeapShaped.alloc (E:=packedTypedEnv)
    (x:=⟨.bytes .memory,.bytes [17,34,51,68]⟩) HeapShaped.empty trivial
  have inner : HeapInner (E:=packedTypedEnv) heap := HeapInner.alloc (E:=packedTypedEnv)
    (x:=⟨.bytes .memory,.bytes [17,34,51,68]⟩) HeapInner.empty trivial
  exact ⟨⟨⟨ok,HeapTy.Le.refl _⟩,trivial⟩,shaped,inner⟩

theorem success_memOK : MemOK packedTypedEnv heap.ty successful.1.1.1 :=
  PhysicalSlotPort.memOK _ _ _ _ _ _ rfl rfl caller_memOK

theorem revert_memOK : MemOK packedTypedEnv heap.ty reverted.1.1.1 := by
  simpa only [actual_revert] using caller_memOK

theorem refused_output_keeps_completion : copyOutput reverted (finish_shared _ _ _ _ _ _ _)
    placement 0 false [17,34,51,68] rfl memory 3 2 = (reverted,none) :=
  copyOutput_refusal _ _ _ _ _ _ _ _ _ _ (by decide)

theorem end_zero_copy : copyAfter reverted (finish_shared _ _ _ _ _ _ _)
    placement 0 false [17,34,51,68] rfl memory 4 3 0 =
      (reverted,some ((memory,caller),(prefixResidual,prefixEncoding),reverted.2)) := by
  have zero : HeapWindow.copyHeapWindow reverted.2.effects reverted.1.1.1.2.heap placement 0 false [17,34,51,68] rfl memory 4 3 0 = some (memory,reverted.1.1.1.2.heap) :=
    HeapWindow.copyHeapWindow_zero reverted.2.effects reverted.1.1.1.2.heap placement 0 false [17,34,51,68] rfl memory 4 3
      (by decide) (by decide) (congrArg Fin.val (bytesObject_header _ _ _ 128)) (bytesObject_payload_list _ _ _ 128)
  simp only [copyAfter,HeapWindow.copyCoupledWindow,HeapWindow.copyStateWindow_heap,zero,
    Option.map_some,withSourceHeap_unchanged]
  simp only [actual_revert]

def parent := caller.2.ex.enter account ⟨account.val+2,by decide⟩ 17 [] false
def invoke : Invoke packedTypedEnv [] := slotInvoke packedTypedRegistry packedTypedRegistry false 7 dirtyBoolThreeRequest.raw
  [0x99,0x88,0x77] "LibraryCode" 0

theorem actual_invoke : invoke observed (enter caller prefixResidual parent .delegatecall ⟨32,by decide⟩ 0 [17,34,51,68])
    .delegatecall ⟨32,by decide⟩ 10000 [17,34,51,68] ⟨⟨caller,prefixResidual⟩,prefixEncoding⟩ =
      some ((.ok (.success [0x99,0x88,0x77]),⟨⟨physical.1.1.1.2,physical.1.1.2⟩,physical.1.2⟩),[]) := by
  simp only [invoke,slotInvoke,representedFrameWrite?,Option.map_map,Function.comp_def]
  change dirtyBoolThreePrepared.map _ = _
  rw [← Option.some_get dirty_bool_three_prepares,Option.map_some]
  rfl

theorem actual_call_driver : call invoke caller prefixResidual prefixEncoding observed rfl memory parent .delegatecall
    ⟨32,by decide⟩ 10000 0 160 4 =
      some (.ok (.success [0x99,0x88,0x77]),finish caller prefixEncoding observed
        (enter caller prefixResidual parent .delegatecall ⟨32,by decide⟩ 0 [17,34,51,68])
        ⟨⟨physical.1.1.1.2,physical.1.1.2⟩,physical.1.2⟩ [] (.success [0x99,0x88,0x77])) := by
  apply call_normal_rule invoke caller prefixResidual prefixEncoding observed rfl memory parent .delegatecall
    ⟨32,by decide⟩ 10000 0 160 4 [17,34,51,68] ⟨⟨physical.1.1.1.2,physical.1.1.2⟩,physical.1.2⟩ []
    (.success [0x99,0x88,0x77]) rfl _ actual_invoke
  rw [PhysicalHeapPort.load_view _ _ _ (by decide)]
  exact congrArg some (bytesObject_payload_list _ _ _ 128)

def driverCompleted := finish caller prefixEncoding observed
  (enter caller prefixResidual parent .delegatecall ⟨32,by decide⟩ 0 [17,34,51,68])
  ⟨⟨physical.1.1.1.2,physical.1.1.2⟩,physical.1.2⟩ [] (.success [0x99,0x88,0x77])

theorem actual_driver_completion : call invoke caller prefixResidual prefixEncoding observed rfl memory parent .delegatecall
    ⟨32,by decide⟩ 10000 0 160 4 = some (.ok (.success [0x99,0x88,0x77]),driverCompleted) := actual_call_driver

theorem driver_output : copyOutput driverCompleted (finish_shared _ _ _ _ _ _ _)
    placement 0 false [17,34,51,68] rfl memory 1 2 =
      (driverCompleted,some ((Solidity.Backend.Environment.writeBytes memory 161 [0x99,0x88],
        withSourceHeap driverCompleted.1.1.1 (heap.write 0 (.bytes [17,0x99,0x88,68]) rfl)),
        (driverCompleted.1.1.2,driverCompleted.1.2),driverCompleted.2)) :=
  copyOutput_exact driverCompleted (finish_shared _ _ _ _ _ _ _) placement 0 false [17,34,51,68] rfl memory 1 2
    (by decide) (congrArg Fin.val (bytesObject_header _ _ _ 128)) (bytesObject_payload_list _ _ _ 128)

def driverPlacement := HeapWindow.windowPlacement heap placement 0 false [17,34,51,68] [0x99,0x88] rfl 1 (by decide)
theorem driver_placement : driverPlacement.address=placement.address ∧ driverPlacement.shape=placement.shape ∧
    driverPlacement.free=placement.free := HeapWindow.windowPlacement_choices _ _ _ _ _ _ _ _ _

def wrongObserved : ObservedEffects packedTypedEnv.layout packedTypedEnv.lay packedTypedEnv.lay :=
  ⟨⟨caller.2.ex.apply (.account ⟨32,by decide⟩ (fun a=>{a with nonce:=9})),observed.effects.logs,observed.effects.returndata⟩,
    observed.trace,observed.logs_eq⟩

theorem wrong_entry_world : wrongObserved.effects.execution≠caller.2.ex := by
  intro h
  have lengths := congrArg (fun ex=>ex.journal.length) h
  change 2=1 at lengths
  cases lengths

def environmentTrace (out : Outcome) : List Observation :=
  [.event (.call ⟨32,by decide⟩ 0 [17,34,51,68] true),.event (.answer out none)]
def environmentCarrier (out : Outcome) : Carrier packedTypedEnv [] :=
  ⟨⟨(caller.1,{caller.2 with events:=caller.2.events++
    [.call ⟨32,by decide⟩ 0 [17,34,51,68] true,.answer out none]}),prefixResidual⟩,prefixEncoding⟩

theorem actual_source_static_invoke (G : Glob packedTypedEnv) (out : Outcome) :
    staticEnvironmentInvoke G out observed (enter caller prefixResidual parent .staticcall ⟨32,by decide⟩ 0 [17,34,51,68])
      .staticcall ⟨32,by decide⟩ 10000 [17,34,51,68] ⟨⟨caller,prefixResidual⟩,prefixEncoding⟩ =
        some ((.ok out,environmentCarrier out),environmentTrace out) := by
  cases out <;> rfl

theorem actual_source_static_call (G : Glob packedTypedEnv) (out : Outcome) :
    call (staticEnvironmentInvoke G out) caller prefixResidual prefixEncoding observed rfl memory parent .staticcall
      ⟨32,by decide⟩ 10000 0 160 4 =
        some (.ok out,finish caller prefixEncoding observed
          (enter caller prefixResidual parent .staticcall ⟨32,by decide⟩ 0 [17,34,51,68])
          (environmentCarrier out) (environmentTrace out) out) := by
  apply call_normal_rule (staticEnvironmentInvoke G out) caller prefixResidual prefixEncoding observed rfl memory parent .staticcall
    ⟨32,by decide⟩ 10000 0 160 4 [17,34,51,68] (environmentCarrier out) (environmentTrace out) out
    rfl _ (actual_source_static_invoke G out)
  rw [PhysicalHeapPort.load_view _ _ _ (by decide)]
  exact congrArg some (bytesObject_payload_list _ _ _ 128)

theorem environment_kind_refusal (G : Glob packedTypedEnv) (out : Outcome) :
    staticEnvironmentInvoke G out observed
      (enter caller prefixResidual parent .staticcall ⟨32,by decide⟩ 0 [17,34,51,68])
      .delegatecall ⟨32,by decide⟩ 10000 [17,34,51,68] ⟨⟨caller,prefixResidual⟩,prefixEncoding⟩=none := rfl

def environmentCompleted (out : Outcome) := finish caller prefixEncoding observed
  (enter caller prefixResidual parent .staticcall ⟨32,by decide⟩ 0 [17,34,51,68])
  (environmentCarrier out) (environmentTrace out) out

theorem environment_finish (out : Outcome) : environmentCompleted out =
    (environmentCarrier out,⟨⟨caller.2.ex,committedLogs (observed.trace++environmentTrace out),returnData out⟩,
      observed.trace++environmentTrace out,rfl⟩) := by
  cases out <;> rfl

theorem source_environment_composition (G : Glob packedTypedEnv) (out : Outcome) :
    call (staticEnvironmentInvoke G out) caller prefixResidual prefixEncoding observed rfl memory parent .staticcall
      ⟨32,by decide⟩ 10000 0 160 4 =
        some (.ok out,(environmentCarrier out,
          ⟨⟨caller.2.ex,committedLogs (observed.trace++environmentTrace out),returnData out⟩,
            observed.trace++environmentTrace out,rfl⟩)) := by
  rw [actual_source_static_call G out]
  exact congrArg (fun x : Result packedTypedEnv [] => some ((Except.ok out : Except Halt Outcome),x)) (environment_finish out)

theorem source_environment_revert_output : copyOutput (environmentCompleted (.revert [0xde,0xad,0xbe]))
    rfl placement 0 false [17,34,51,68] rfl memory 1 2 =
      (environmentCompleted (.revert [0xde,0xad,0xbe]),
        some ((Solidity.Backend.Environment.writeBytes memory 161 [0xde,0xad],
          withSourceHeap (environmentCarrier (.revert [0xde,0xad,0xbe])).1.1
            (heap.write 0 (.bytes [17,0xde,0xad,68]) rfl)),
          (prefixResidual,prefixEncoding),(environmentCompleted (.revert [0xde,0xad,0xbe])).2)) :=
  copyOutput_exact (environmentCompleted (.revert [0xde,0xad,0xbe])) rfl placement 0 false [17,34,51,68] rfl memory 1 2
    (by decide) (congrArg Fin.val (bytesObject_header _ _ _ 128)) (bytesObject_payload_list _ _ _ 128)

def codeCarrier : Carrier packedTypedEnv [] :=
  ⟨⟨(caller.1,{caller.2 with ex:=caller.2.ex.apply (.account ⟨32,by decide⟩ (fun a=>{a with code:=some 7}))}),
    prefixResidual⟩,prefixEncoding⟩

theorem environment_known_code_refusal (G : Glob packedTypedEnv) (out : Outcome) :
    staticEnvironmentInvoke G out observed (enter caller prefixResidual parent .staticcall ⟨32,by decide⟩ 0 [17,34,51,68])
      .staticcall ⟨32,by decide⟩ 10000 [17,34,51,68] codeCarrier=none := rfl

theorem precompile_refused (G : Glob packedTypedEnv) (out : Outcome) :
    staticEnvironmentInvoke G out observed (enter caller prefixResidual parent .staticcall ⟨2,by decide⟩ 0 [17,34,51,68])
      .staticcall ⟨2,by decide⟩ 10000 [17,34,51,68] ⟨⟨caller,prefixResidual⟩,prefixEncoding⟩=none := rfl

theorem zero_refused (G : Glob packedTypedEnv) (out : Outcome) :
    staticEnvironmentInvoke G out observed (enter caller prefixResidual parent .staticcall 0 0 [17,34,51,68])
      .staticcall 0 10000 [17,34,51,68] ⟨⟨caller,prefixResidual⟩,prefixEncoding⟩=none := rfl

theorem unclassified_code_refused (G : Glob packedTypedEnv) (out : Outcome) :
    staticEnvironmentInvoke G out observed (enter caller prefixResidual parent .staticcall ⟨33,by decide⟩ 0 [17,34,51,68])
      .staticcall ⟨33,by decide⟩ 10000 [17,34,51,68] ⟨⟨caller,prefixResidual⟩,prefixEncoding⟩=none := rfl

end Solidity.Yul.World.PhysicalCompletionChecks
