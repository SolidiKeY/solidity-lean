import Solidity.Yul.World.PhysicalHeapPort
import Solidity.Yul.World.PhysicalSlotPort
import Solidity.Yul.Views.ByteHeapRealizationControls
import Solidity.Yul.Views.OwnedBoolDeclarationControls
import Solidity.Yul.World.WorldChecks

/-! Actual VY2 carriers/controls composed with world consumers. These are not
callee reachability, universal allocation or common source-emit adequacy. -/
namespace Solidity.Yul.World.PhysicalPortChecks
open Solidity.Source
open Solidity.Roadmap (Bytes Word)
open Solidity.Source.StateExamples (addr)
open Solidity.Yul.Views
open Solidity.Yul.Views.Controls

def callerState : Source.EMState heapByteEnv [.bytes .memory,.string .memory] :=
  ⟨byteState.1,{byteState.2 with
    ex := byteState.2.ex.apply (.account (addr 1) (fun a => {a with nonce:=1,balance:=toWord 23,code:=some 7})),
    events := [.credit (addr 1) (toWord 3)],logs := [(addr 1,[119])]}⟩

theorem caller_memOK : Source.MemOK heapByteEnv byteHeap.ty callerState := by
  have ok := actual_initial_MemOK
  exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2.1,ok.2.2⟩

def returnEntry : Effects heapByteEnv.layout heapByteEnv.lay heapByteEnv.lay :=
  ⟨callerState.2.ex,[],[9,0x99,0x88,0x77]⟩

theorem caller_nonempty : callerState.2.ex.journal.length = 1 ∧ callerState.2.events ≠ [] ∧
    callerState.2.logs ≠ [] := by decide

theorem realized_load : PhysicalHeapPort.port.load (encodeByteHeap (bytePlacement 0) actualByteEntries heapByteResidual)
    (PhysicalHeapPort.payloadOffset byteHeap (bytePlacement 0) 0 false byteOld rfl)
    ⟨byteOld.length,by decide⟩ = some byteOld :=
  PhysicalHeapPort.load_encoded byteHeap (bytePlacement 0) actualByteEntries actual_entries_distinct
    ⟨0,false,byteOld,rfl⟩ List.mem_cons_self heapByteResidual

theorem actual_copy : PhysicalHeapPort.copyWriteback returnEntry byteHeap (bytePlacement 0) 0 false byteOld rfl bytePhysical 1 3 =
    some (Solidity.Backend.Environment.writeBytes bytePhysical 160 byteNew,heapByteAfter) :=
  PhysicalHeapPort.copyWriteback_exact _ _ _ _ _ _ _ _ _ _ _ rfl rfl (by decide)

theorem physical_and_heap_frame :
    (PhysicalHeapPort.copyWriteback returnEntry byteHeap (bytePlacement 0) 0 false byteOld rfl bytePhysical 1 3).map
      (fun result => (result.1 191,result.2.get 1,result.2.ty,result.2.next)) =
      some (bytePhysical 191,byteHeap.get 1,byteHeap.ty,byteHeap.next) :=
  PhysicalHeapPort.copyWriteback_frame _ _ _ _ 1 191 _ _ _ _ _ _ _ rfl rfl (by decide) (by decide) (Or.inr (by decide))

theorem copied_alias :
    (PhysicalHeapPort.copyWriteback returnEntry byteHeap (bytePlacement 0) 0 false byteOld rfl bytePhysical 1 3).map
      (fun result => (result.2.get 0,readBytes result.1 160 3)) =
      some (some ⟨heapByteType false,heapByteData heapByteEnv.layout false byteNew⟩,byteNew) := by
  rw [actual_copy]
  simp only [Option.map_some]
  apply congrArg some
  apply Prod.ext
  · exact Source.Heap.write_get byteHeap 0 (heapByteData heapByteEnv.layout false byteNew) rfl
  · exact Solidity.Backend.Environment.read_written _ _ _

theorem exact_end_zero : PhysicalHeapPort.copyWriteback returnEntry byteHeap (bytePlacement 0) 0 false byteOld rfl bytePhysical 4 0 =
    some (bytePhysical,byteHeap) := by
  change (heapByteWriteback byteHeap (bytePlacement 0) 0 false byteOld rfl bytePhysical).bind
    (fun heap => some (bytePhysical,heap)) = _
  rw [byte_unchanged_whole_heap]
  rfl

theorem out_of_bounds_zero : PhysicalHeapPort.copyWriteback returnEntry byteHeap (bytePlacement 0) 0 false byteOld rfl bytePhysical 5 0 = none :=
  PhysicalHeapPort.copyWriteback_bounds _ _ _ _ _ _ _ _ _ _ (by decide)

theorem wrong_region_and_stale :
    PhysicalHeapPort.port.load bytePhysical 288 3 ≠ some byteOld ∧
    (PhysicalHeapPort.copyWriteback returnEntry byteHeap (bytePlacement 0) 0 false byteOld rfl bytePhysical 1 3).map
      (fun result => readBytes result.1 160 3) ≠ some byteOld := by
  rw [actual_copy]
  decide

def stateResult := withSourceHeap callerState heapByteAfter

theorem actual_state_copy : PhysicalHeapPort.copyStateWriteback returnEntry callerState (bytePlacement 0)
    0 false byteOld rfl bytePhysical 1 3 =
    some (Solidity.Backend.Environment.writeBytes bytePhysical 160 byteNew,stateResult) := by
  change (heapByteWriteback byteHeap (bytePlacement 0) 0 false byteOld rfl
      (Solidity.Backend.Environment.writeBytes bytePhysical 160 byteNew)).map
    (fun heap => (Solidity.Backend.Environment.writeBytes bytePhysical 160 byteNew,withSourceHeap callerState heap)) = _
  have hc := actual_copy
  change (heapByteWriteback byteHeap (bytePlacement 0) 0 false byteOld rfl
      (Solidity.Backend.Environment.writeBytes bytePhysical 160 byteNew)).map
    (fun heap => (Solidity.Backend.Environment.writeBytes bytePhysical 160 byteNew,heap)) = _ at hc
  obtain ⟨heap,hw,he⟩ := Option.map_eq_some_iff.mp hc
  have pair := Prod.mk.inj he
  cases pair.2
  rw [hw]
  rfl

theorem real_memOK : Source.MemOK heapByteEnv byteHeap.ty stateResult :=
  PhysicalHeapPort.copyStateWriteback_memOK _ _ _ _ _ _ _ _ _ _ _ _ _ actual_state_copy caller_memOK

theorem real_prefix : stateResult.1 = callerState.1 ∧ stateResult.2.ex = callerState.2.ex ∧
    stateResult.2.events = callerState.2.events ∧ stateResult.2.logs = callerState.2.logs :=
  PhysicalHeapPort.copyStateWriteback_prefix _ _ _ _ _ _ _ _ _ _ _ _ actual_state_copy

def slotEntry : ObservedEffects packedTypedEnv.layout packedTypedEnv.lay packedTypedEnv.lay :=
  ⟨⟨dirtyBoolRun.1.1.2.2.ex,committedLogs Checks.callerTrace,[9,8,7]⟩,Checks.callerTrace,rfl⟩

def slotResult := PhysicalSlotPort.step packedTypedRegistry packedTypedRegistry dirtyBoolThreeRequest dirtyBoolRun.2
  packedStepFrame dirtyBoolThreePlan dirtyBoolRun.1.1.2 dirtyBoolRun.1.2 slotEntry rfl rfl

theorem slot_raw_and_prefix :
    reencodePersistentSlot (representedBanks packedTypedRegistry false slotResult.1.2)
      ⟨slotResult.2.effects.execution,slotResult.1.1.2⟩ account 7 = some dirtyBoolThreeRequest.raw ∧
    slotResult.2.trace = Checks.callerTrace ∧ slotResult.2.effects.returndata = [9,8,7] :=
  ⟨PhysicalSlotPort.persistent_word _ _ _ _ _ rfl rfl rfl rfl ((packedSeparationCheck_iff _).mp (by decide)),rfl,rfl⟩

theorem caller_journals_retained : slotEntry.effects.execution.journal.length = 1 ∧
    dirtyBoolRun.1.2.journal.length = 1 ∧ dirtyBoolRun.2.journal.length > 0 := by decide

theorem coupled_child_rollback :
    companionRollback (companionEnter ⟨slotEntry.effects.execution,dirtyBoolRun.1.2⟩ account account 0 [] false)
      ⟨slotResult.2.effects.execution,slotResult.1.1.2⟩ = ⟨slotEntry.effects.execution,dirtyBoolRun.1.2⟩ ∧
    boolEncodingRollback dirtyBoolRun.2.journal.length slotResult.1.2 = dirtyBoolRun.2 ∧
    slotResult.2.trace = slotEntry.trace := PhysicalSlotPort.rollback _ _ _ _ _ rfl rfl rfl

theorem static_coupled :
    let result := PhysicalSlotPort.step packedTypedRegistry packedTypedRegistry dirtyBoolThreeRequest dirtyBoolRun.2
      {packedStepFrame with static:=true} dirtyBoolThreePlan dirtyBoolRun.1.1.2 dirtyBoolRun.1.2 slotEntry rfl rfl
    result.1 = (((.error (.revert []),dirtyBoolRun.1.1.2),dirtyBoolRun.1.2),dirtyBoolRun.2) ∧
    result.2.effects.execution = slotEntry.effects.execution ∧ result.2.trace = slotEntry.trace ∧
    result.2.effects.returndata = slotEntry.effects.returndata := PhysicalSlotPort.static_result _ _ _ _ _ rfl rfl rfl

theorem wrong_owner_rejected : dirtyBoolThreeRequest.address ≠
    ({packedStepFrame with this:=⟨account.val+1,by decide⟩} : Source.Fr).this := by decide

theorem reserved_after_copy : ReservedOK
    (Solidity.Backend.Environment.writeBytes bytePhysical 160 byteNew) (bytePlacement 0).free :=
  PhysicalHeapPort.copyWriteback_reserved byteHeap (bytePlacement 0) 0 false byteOld byteNew rfl bytePhysical actual_heap_realizes.1

theorem actual_copy_rule : AdapterRules.Box
    (AdapterRules.CopyStep PhysicalHeapPort.port 160 1 3)
    (fun after => after.observed = (⟨⟨callerState.2.ex,[],returnEntry.returndata⟩,[],rfl⟩ :
      ObservedEffects heapByteEnv.layout heapByteEnv.lay heapByteEnv.lay) ∧
      after.memory = Solidity.Backend.Environment.writeBytes bytePhysical 160 byteNew)
    ⟨⟨⟨callerState.2.ex,[],returnEntry.returndata⟩,[],rfl⟩,bytePhysical⟩ :=
  PhysicalHeapPort.raw_copy_rule _ _ _ _ _ byteNew rfl (by decide)

def thirdRequest : PackedSlotRequest := ⟨false,account,7,⟨0xabcdef000004,by decide⟩⟩
def thirdPrepared := prepareRepresentedSlot packedTypedRegistry packedTypedRegistry thirdRequest
  (requestEncoding packedTypedRegistry packedTypedRegistry dirtyBoolThreeRequest dirtyBoolRun.2)
theorem third_prepares : thirdPrepared.isSome := by decide
def thirdPlan := thirdPrepared.get third_prepares

def slotSecond := PhysicalSlotPort.step packedTypedRegistry packedTypedRegistry thirdRequest
  (requestEncoding packedTypedRegistry packedTypedRegistry dirtyBoolThreeRequest dirtyBoolRun.2)
  packedStepFrame thirdPlan slotResult.1.1.1.2 slotResult.1.1.2 slotResult.2 rfl rfl

theorem full_outer_rollback :
    companionRollback (companionEnter ⟨slotEntry.effects.execution,dirtyBoolRun.1.2⟩ account account 0 [] false)
      (companionCommit (companionEnter ⟨slotResult.2.effects.execution,slotResult.1.1.2⟩ account account 0 [] false)
        ⟨slotSecond.2.effects.execution,slotSecond.1.1.2⟩) = ⟨slotEntry.effects.execution,dirtyBoolRun.1.2⟩ ∧
    boolEncodingRollback dirtyBoolRun.2.journal.length slotSecond.1.2 = dirtyBoolRun.2 ∧
    slotSecond.2.trace = slotEntry.trace :=
  PhysicalSlotPort.two_outer_rollback _ _ _ _ _ rfl rfl thirdRequest thirdPlan rfl rfl

theorem slot_actual_memOK : Source.MemOK packedTypedEnv packedTypedState.2.heap.ty slotResult.1.1.1.2 :=
  PhysicalSlotPort.memOK _ _ _ _ _ _ rfl rfl (dirty_bool_every_H _ packed_typed_initial_MemOK)

theorem mismatched_world_rejected : slotEntry.effects.execution ≠ packedTypedState.2.ex := by
  intro same
  have size := congrArg (fun ex => ex.journal.length) same
  contradiction

def callEntry : ObservedEffects heapByteEnv.layout heapByteEnv.lay heapByteEnv.lay :=
  ⟨⟨callerState.2.ex,committedLogs Checks.callerTrace,[9,8,7,6]⟩,Checks.callerTrace,rfl⟩
def callParent := callerState.2.ex.enter (addr 1) (addr 3) (toWord 5) [] false

def callAnswer (code : Roadmap.Address) (input : Bytes) : FrameAnswer heapByteEnv.layout heapByteEnv.lay heapByteEnv.lay :=
  ⟨[.account (addr 1) (fun a => {a with nonce:=a.nonce+1})],
    [.event (.call code (toWord 5) input false)] ++ Checks.calleeTrace,.revert byteNew⟩
def callProducer : WorldPort heapByteEnv.layout heapByteEnv.lay heapByteEnv.lay :=
  fun _ _ code _ _ input => some (callAnswer code input)

/-- Actual physical view→delegate input→completion→output path. The producer
is a scripted interface control, not certified executable known/env code. -/
theorem physical_delegate_call :
    (callAdapter PhysicalHeapPort.port callProducer callEntry bytePhysical callParent .delegatecall (addr 2)
      (toWord 100000) (toWord 0) 160 3 160 3).map
      (fun c => (c.observed.effects.execution,c.observed.trace,c.outcome,
        c.copiedMemory.map (fun m => readBytes m 160 3))) =
      some (callerState.2.ex,rollbackTrace Checks.callerTrace (callAnswer (addr 2) byteOld).trace,
        .revert byteNew,some byteNew) := by
  have load : PhysicalHeapPort.port.load bytePhysical 160 3 = some byteOld := by
    rw [← actual_heap_constructed]
    exact realized_load
  rw [callAdapter_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl load rfl]
  change some ((complete callEntry.effects (addr 1) (addr 3) (toWord 5) byteOld false
    (callAnswer (addr 2) byteOld).operations (committedLogs (callAnswer (addr 2) byteOld).trace)
    (.revert byteNew)).execution,rollbackTrace Checks.callerTrace (callAnswer (addr 2) byteOld).trace,
    (.revert byteNew : Roadmap.Outcome),some (readBytes (Solidity.Backend.Environment.writeBytes bytePhysical 160 byteNew) 160 3)) = _
  rw [complete_revert]
  rfl

theorem actual_source_alias_read :
    (Source.bytesOfRV (E:=heapByteEnv) byteReadFrame 1 (.val (stateResult.1.get .here))).run stateResult =
      (.ok byteNew,stateResult) ∧
    (Source.readLoc (E:=heapByteEnv) byteReadFrame (.memByte 0 0)).run stateResult =
      (.ok (.fixedBytes [0x99] rfl),stateResult) := ⟨rfl,rfl⟩

def stringEntry : Effects heapByteEnv.layout heapByteEnv.lay heapByteEnv.lay :=
  ⟨callerState.2.ex,[],stringNew⟩

theorem actual_string_copy : PhysicalHeapPort.copyWriteback stringEntry byteHeap (bytePlacement 0) 1 true stringOld rfl
    bytePhysical 0 33 = some (Solidity.Backend.Environment.writeBytes bytePhysical 288 stringNew,
      byteHeap.write 1 (heapByteData heapByteEnv.layout true stringNew) rfl) := by
  have header := (actual_heap_reads ⟨1,true,stringOld,rfl⟩ (List.mem_cons_of_mem _ List.mem_cons_self)).1
  exact PhysicalHeapPort.copyWriteback_exact _ _ _ _ _ _ stringNew _ _ _ _ rfl rfl header

def transientRequest : PackedSlotRequest := ⟨true,account,7,⟨0xabcdef000004,by decide⟩⟩
def transientPrepared := prepareRepresentedSlot packedTypedRegistry packedTypedRegistry transientRequest dirtyBoolRun.2
theorem transient_prepares : transientPrepared.isSome := by decide
def transientPlan := transientPrepared.get transient_prepares
def transientResult := PhysicalSlotPort.step packedTypedRegistry packedTypedRegistry transientRequest dirtyBoolRun.2
  packedStepFrame transientPlan dirtyBoolRun.1.1.2 dirtyBoolRun.1.2 slotEntry rfl rfl

theorem transient_exact :
    reencodeTransientSlot (representedBanks packedTypedRegistry true transientResult.1.2)
      ⟨transientResult.2.effects.execution,transientResult.1.1.2⟩ account 7 = some transientRequest.raw ∧
    transientResult.2.effects.execution.world = slotEntry.effects.execution.world ∧
    transientResult.2.trace = slotEntry.trace :=
  ⟨PhysicalSlotPort.transient_word _ _ _ _ _ rfl rfl rfl rfl ((packedSeparationCheck_iff _).mp (by decide)),rfl,rfl⟩

theorem transient_coupled_rollback :
    companionRollback (companionEnter ⟨slotEntry.effects.execution,dirtyBoolRun.1.2⟩ account account 0 [] false)
      ⟨transientResult.2.effects.execution,transientResult.1.1.2⟩ = ⟨slotEntry.effects.execution,dirtyBoolRun.1.2⟩ ∧
    boolEncodingRollback dirtyBoolRun.2.journal.length transientResult.1.2 = dirtyBoolRun.2 ∧
    transientResult.2.trace = slotEntry.trace := PhysicalSlotPort.rollback _ _ _ _ _ rfl rfl rfl

def delegatedFrame (static : Bool) : Source.Fr :=
  PhysicalSlotPort.sourceFrame
    (childContext slotEntry.effects.execution (slotEntry.effects.execution.enter account ⟨account.val+2,by decide⟩ 17 [] static)
      .delegatecall ⟨account.val+1,by decide⟩ 0 []) "LibraryCode" true 0

theorem actual_delegated_slot : (delegatedFrame false).this = account ∧
    (delegatedFrame false).this ≠ (⟨account.val+1,by decide⟩ : Roadmap.Address) ∧
    (PhysicalSlotPort.frameWrite? packedTypedRegistry packedTypedRegistry (delegatedFrame false) false 7
      dirtyBoolThreeRequest.raw dirtyBoolRun.2 dirtyBoolRun.1.1.2 dirtyBoolRun.1.2 slotEntry rfl).map
      (fun result => result.1.1.1.2.2.ex.world.accounts account |>.storage.read finiteFlag) = some (some (.bool true)) := by
  refine ⟨rfl,by decide,?_⟩
  change (dirtyBoolThreePrepared.map (fun p => PhysicalSlotPort.step packedTypedRegistry packedTypedRegistry
    dirtyBoolThreeRequest dirtyBoolRun.2 (delegatedFrame false) p dirtyBoolRun.1.1.2 dirtyBoolRun.1.2 slotEntry rfl rfl)).map _ = _
  rw [← Option.some_get dirty_bool_three_prepares,Option.map_some,Option.map_some]
  rfl

theorem nested_static_delegate :
    (PhysicalSlotPort.frameWrite? packedTypedRegistry packedTypedRegistry (delegatedFrame true) false 7
      dirtyBoolThreeRequest.raw dirtyBoolRun.2 dirtyBoolRun.1.1.2 dirtyBoolRun.1.2 slotEntry rfl).map
      (fun result => result.1.1.1.1) = some (.error (.revert [])) := by
  change (dirtyBoolThreePrepared.map (fun p => PhysicalSlotPort.step packedTypedRegistry packedTypedRegistry
    dirtyBoolThreeRequest dirtyBoolRun.2 (delegatedFrame true) p dirtyBoolRun.1.1.2 dirtyBoolRun.1.2 slotEntry rfl rfl)).map _ = _
  rw [← Option.some_get dirty_bool_three_prepares,Option.map_some,Option.map_some]
  rfl

def delegatedResult := PhysicalSlotPort.step packedTypedRegistry packedTypedRegistry dirtyBoolThreeRequest dirtyBoolRun.2
  (delegatedFrame false) dirtyBoolThreePlan dirtyBoolRun.1.1.2 dirtyBoolRun.1.2 slotEntry rfl rfl

theorem delegated_public_result :
    PhysicalSlotPort.frameWrite? packedTypedRegistry packedTypedRegistry (delegatedFrame false) false 7
      dirtyBoolThreeRequest.raw dirtyBoolRun.2 dirtyBoolRun.1.1.2 dirtyBoolRun.1.2 slotEntry rfl = some delegatedResult := by
  change dirtyBoolThreePrepared.map (fun p => PhysicalSlotPort.step packedTypedRegistry packedTypedRegistry
    dirtyBoolThreeRequest dirtyBoolRun.2 (delegatedFrame false) p dirtyBoolRun.1.1.2 dirtyBoolRun.1.2 slotEntry rfl rfl) = some delegatedResult
  rw [← Option.some_get dirty_bool_three_prepares,Option.map_some]
  rfl

theorem delegated_changed_word_and_code_frame :
    reencodePersistentSlot (representedBanks packedTypedRegistry false delegatedResult.1.2)
      ⟨delegatedResult.2.effects.execution,delegatedResult.1.1.2⟩ account 7 = some dirtyBoolThreeRequest.raw ∧
    delegatedResult.1.2.cells (ownedByteKey false account packedTypedFlag) = ⟨⟨3,by decide⟩,by decide⟩ ∧
    dirtyBoolRun.2.cells (ownedByteKey false account packedTypedFlag) = ⟨⟨2,by decide⟩,by decide⟩ ∧
    delegatedResult.2.effects.execution.world.accounts ⟨account.val+1,by decide⟩ =
      slotEntry.effects.execution.world.accounts ⟨account.val+1,by decide⟩ ∧
    (delegatedFrame false).sender = (⟨account.val+2,by decide⟩ : Roadmap.Address) ∧
    (delegatedFrame false).value = 17 :=
  ⟨PhysicalSlotPort.persistent_word _ _ _ _ _ rfl rfl rfl rfl ((packedSeparationCheck_iff _).mp (by decide)),
    rfl,rfl,rfl,rfl,rfl⟩

/-- LOG0 through LOG4 consume the actual copied VY2 bytes and preserve the
complete caller observation prefix. This is not Source emit topic encoding. -/
theorem physical_log (count : Fin 5) (topics : Vector Word count.val) :
    logAdapter PhysicalHeapPort.port callEntry (Solidity.Backend.Environment.writeBytes bytePhysical 160 byteNew)
      false (addr 1) count topics 160 3 =
      some (emitObserved callEntry ⟨addr 1,count,topics,byteNew⟩) := by
  apply logAdapter_exact
  rw [PhysicalHeapPort.load_view _ _ _ (by decide)]
  exact congrArg some (Solidity.Backend.Environment.read_written _ _ _)

theorem physical_log_rule (count : Fin 5) (topics : Vector Word count.val) :
    AdapterRules.Box (AdapterRules.LogStep PhysicalHeapPort.port false (addr 1) count topics 160 3)
      (fun after => after.observed = emitObserved callEntry ⟨addr 1,count,topics,byteNew⟩ ∧
        after.memory = Solidity.Backend.Environment.writeBytes bytePhysical 160 byteNew)
      ⟨callEntry,Solidity.Backend.Environment.writeBytes bytePhysical 160 byteNew⟩ :=
  AdapterRules.log_step_eq _ _ _ _ _ _ _ _ (physical_log count topics)

theorem physical_log_full_trace (count : Fin 5) (topics : Vector Word count.val) :
    (emitObserved callEntry ⟨addr 1,count,topics,byteNew⟩).trace =
      Checks.callerTrace ++ [.log ⟨addr 1,count,topics,byteNew⟩] ∧
    logAdapter PhysicalHeapPort.port callEntry bytePhysical true (addr 1) count topics 160 3 = none := ⟨rfl,rfl⟩

theorem other_string_image_preserved :
    (MemoryImage.string (p:=bytePlacement 0) stringOld (by decide)).Reads
      (Solidity.Backend.Environment.writeBytes bytePhysical 160 byteNew) 256 := by
  have reads := actual_heap_reads ⟨1,true,stringOld,rfl⟩ (List.mem_cons_of_mem _ List.mem_cons_self)
  exact PhysicalHeapPort.copyWriteback_other_image returnEntry byteHeap (bytePlacement 0) 0 1 false byteOld byteNew
    rfl bytePhysical 1 3 rfl rfl (by decide) _ heapByteAfter actual_copy
    (MemoryImage.string stringOld (by decide)) rfl (by decide) reads

end Solidity.Yul.World.PhysicalPortChecks
