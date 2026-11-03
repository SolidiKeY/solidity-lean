import Solidity.Yul.Views.DynamicNegativeControls
import Solidity.Yul.Views.DynamicPlanRequests

namespace Solidity.Yul.Views.Controls

/-- This companion scalar's declared transient bank is checked below. No
claim of dynamic-array transient declaration layout follows from reuse. -/
def dynTempRegistry (a : Roadmap.Address) : List (ScalarPath dynEnv.layout (dynEnv.lay a)) :=
  [⟨dynPath "temp",0,intField unsigned16 0 (by decide),intCodec _ unsigned16 0 (by decide),.int unsigned16⟩]

theorem dyn_temp_actual_bank : dynEnv.transientRoot (dynPath "temp") = true := rfl

def dynResidual := initialPackedComplement dynRegistry dynTempRegistry (fun k => dynSnapshot k.slot)
def dynCore : ResidualCompanion dynEnv.layout dynEnv.lay dynEnv.lay complementCarrierOwnership := ⟨dynStorageState.2.ex,dynResidual⟩
def dynRequests : List PackedSlotRequest := [⟨false,account,43,2⟩,⟨false,account,1000,12⟩,
  ⟨false,account,1001,dynMax⟩,⟨false,account,45,1⟩,⟨false,account,2000,33⟩]

theorem dyn_plans_ready : (dynRequests.mapM (preparePackedSlot dynRegistry dynTempRegistry)).isSome := by decide

def dynPlans := (dynRequests.mapM (preparePackedSlot dynRegistry dynTempRegistry)).get dyn_plans_ready

theorem dyn_plan_requests : dynPlans.map PackedSlotPlan.request = dynRequests :=
  packedPlanRequests dynRequests dynPlans (Option.get_mem dyn_plans_ready)

theorem dyn_caller_other_address : ∀ p ∈ dynPlans, (⟨2,by decide⟩ : Roadmap.Address) ≠ p.request.address := by
  intro p member
  have requested : p.request ∈ dynRequests := by
    rw [← dyn_plan_requests]; exact List.mem_map.mpr ⟨p,member,rfl⟩
  exact (by decide : ∀ q ∈ dynRequests, (⟨2,by decide⟩ : Roadmap.Address) ≠ q.address) p.request requested

theorem dyn_caller_other_slot (q : Roadmap.Word) (notUsed : ∀ r ∈ dynRequests, q ≠ r.slot) :
    ∀ p ∈ dynPlans, q ≠ p.request.slot := by
  intro p member
  apply notUsed p.request
  rw [← dyn_plan_requests]
  exact List.mem_map.mpr ⟨p,member,rfl⟩

theorem dyn_registry_no_temp : ∀ c ∈ dynRegistry account, dynPath "temp" ≠ c.path := by
  intro c member same
  have bank : dynEnv.transientRoot c.path = false := by
    rcases List.mem_append.mp member with rootMember | element
    · exact dynComputed.bank_agreement c rootMember
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at element
      rcases element with rfl | rfl | rfl <;> rfl
  rw [← same] at bank
  have yes : dynEnv.transientRoot (dynPath "temp") = true := rfl
  rw [yes] at bank
  cases bank

theorem dyn_temp_registry_no_xs : ∀ c ∈ dynTempRegistry account, dynPath "xs" ≠ c.path := by
  intro c member
  have same := List.mem_singleton.mp member
  subst c
  decide

def dynCaller := runPackedSource packedStepFrame dynPlans dynStorageState dynResidual
def dynCallerCore : ResidualCompanion dynEnv.layout dynEnv.lay dynEnv.lay complementCarrierOwnership := ⟨dynCaller.1.2.2.ex,dynCaller.2⟩

theorem dyn_actual_caller_sequence : dynCallerCore = runPackedSlots dynCore dynPlans :=
  runPackedSource_companion packedStepFrame dynPlans dynStorageState dynResidual rfl

theorem dyn_caller_actual_lengths : (Source.readLen (E := dynEnv) packedStepFrame (dynPath "xs")).run dynCaller.1.2 = (.ok 2,dynCaller.1.2) ∧
    (Source.readLen (E := dynEnv) packedStepFrame (dynPath "ys")).run dynCaller.1.2 = (.ok 1,dynCaller.1.2) := ⟨rfl,rfl⟩

theorem dyn_caller_actual_success : dynCaller.1.1 = .ok () ∧ dynCaller.1.2.2.ex.journal.length = 5 ∧ dynCaller.2.journal.length = 5 := ⟨rfl,rfl,rfl⟩

def dynChildRequests : List PackedSlotRequest := [⟨false,account,1000,888⟩,⟨false,account,43,0⟩,
  ⟨true,account,0,⟨0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd7788,by decide⟩⟩]

theorem dyn_child_ready : (dynChildRequests.mapM (preparePackedSlot dynRegistry dynTempRegistry)).isSome := by decide

def dynChildDataPlan := (preparePackedFrame (ps := dynRegistry) (ts := dynTempRegistry) packedStepFrame false 1000 888).get (by decide)
def dynChildLengthPlan := (preparePackedFrame (ps := dynRegistry) (ts := dynTempRegistry) packedStepFrame false 43 0).get (by decide)
def dynChildTempRaw : Roadmap.Word := ⟨0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd7788,by decide⟩
def dynChildTempPlan := (preparePackedFrame (ps := dynRegistry) (ts := dynTempRegistry) packedStepFrame true 0 dynChildTempRaw).get (by decide)
def dynChildPlans := [dynChildDataPlan,dynChildLengthPlan,dynChildTempPlan]

def dynChild := runPackedSource packedStepFrame dynChildPlans dynCaller.1.2 dynCaller.2
def dynChildCore : ResidualCompanion dynEnv.layout dynEnv.lay dynEnv.lay complementCarrierOwnership := ⟨dynChild.1.2.2.ex,dynChild.2⟩

theorem dyn_actual_child_sequence : dynChildCore = runPackedSlots dynCallerCore dynChildPlans :=
  runPackedSource_companion packedStepFrame dynChildPlans dynCaller.1.2 dynCaller.2 rfl

theorem dyn_child_rollback : companionRollback (companionEnter dynCallerCore account account 0 [] false) dynChildCore = dynCallerCore := by
  rw [dyn_actual_child_sequence]
  exact packed_frame_rollback _ _ _ _ _ _ _

theorem dyn_child_commit_outer_rollback : companionRollback (companionEnter dynCore account account 0 [] false)
    (companionCommit (companionEnter dynCallerCore account account 0 [] false) dynChildCore) = dynCore := by
  rw [dyn_actual_child_sequence,dyn_actual_caller_sequence]
  exact packed_frame_outer_commit _ _ _ _ _ _ _ _

theorem dyn_static_complete_error : runPackedSource {packedStepFrame with static := true} dynChildPlans dynCaller.1.2 dynCaller.2 =
    ((.error (.revert []),dynCaller.1.2),dynCaller.2) := rfl

/-- Actual late source index failure keeps the successfully written prefix;
frame rollback above is a distinct operation, not silent error restoration. -/
theorem dyn_late_index_error_keeps_prefix :
    (Source.indexLoc (E := dynEnv) packedStepFrame dynX.reference 2).run dynCaller.1.2 =
      (.error (.revert (Source.panicData .index)),dynCaller.1.2) := rfl

theorem dyn_frames_every_H (H : Source.HeapTy) (ok : Source.MemOK dynEnv H dynStorageState) :
    Source.MemOK dynEnv H dynChild.1.2 :=
  runPackedSource_MemOK packedStepFrame dynChildPlans dynCaller.1.2 dynCaller.2 H
    (runPackedSource_MemOK packedStepFrame dynPlans dynStorageState dynResidual H ok)

theorem dyn_frames_inhabited_MemOK : Source.MemOK dynEnv dynStorageState.2.heap.ty dynChild.1.2 := dyn_frames_every_H _ dyn_initial_MemOK

def dynAfterDataCore := applyPackedSlot dynCallerCore dynChildDataPlan
def dynAfterLengthCore := applyPackedSlot dynAfterDataCore dynChildLengthPlan

theorem dyn_child_length_request : dynChildLengthPlan.request = ⟨false,account,43,0⟩ :=
  preparePackedSlot_request _ _ (Option.get_mem (by decide))

theorem dyn_child_temp_request : dynChildTempPlan.request = ⟨true,account,0,dynChildTempRaw⟩ :=
  preparePackedSlot_request _ _ (Option.get_mem (by decide))

theorem dyn_child_complete_raw : reencodePersistentSlot dynRegistry dynChildCore account 43 = some 0 ∧
    reencodeTransientSlot dynTempRegistry dynChildCore account 0 = some dynChildTempRaw := by
  rw [dyn_actual_child_sequence]
  change reencodePersistentSlot dynRegistry (applyPackedSlot dynAfterLengthCore dynChildTempPlan) account 43 = some 0 ∧
    reencodeTransientSlot dynTempRegistry (applyPackedSlot dynAfterLengthCore dynChildTempPlan) account 0 = some dynChildTempRaw
  constructor
  · rw [packedTransient_persistent_reencode dynAfterLengthCore dynChildTempPlan (congrArg PackedSlotRequest.transient dyn_child_temp_request)]
    have tr := congrArg PackedSlotRequest.transient dyn_child_length_request
    have sep : finiteSeparated (dynRegistry dynChildLengthPlan.request.address) := by
      rw [dyn_child_length_request]; exact dyn_registry_separated
    have encoded := @packedPersistent_reencode dynEnv.layout dynEnv.lay dynEnv.lay dynRegistry dynTempRegistry dynAfterDataCore dynChildLengthPlan tr sep
    rw [dyn_child_length_request] at encoded
    exact encoded
  · have tr := congrArg PackedSlotRequest.transient dyn_child_temp_request
    have sep : finiteSeparated (dynTempRegistry dynChildTempPlan.request.address) := List.pairwise_singleton _ _
    have encoded := @packedTransient_reencode dynEnv.layout dynEnv.lay dynEnv.lay dynRegistry dynTempRegistry dynAfterLengthCore dynChildTempPlan tr sep
    rw [dyn_child_temp_request] at encoded
    exact encoded

theorem dyn_child_reset :
    (companionEndTx dynChildCore).source.world = dynChildCore.source.world ∧
    ((companionEndTx dynChildCore).source.transient.cells account).read (dynPath "temp") = some (.int 0 (by decide)) ∧
    (companionEndTx dynChildCore).residual.cells (complementKey true account 0) = 0 := by
  have p := companionEndTx_persistent dynChildCore (complementKey false account 43) rfl
  have t := companionEndTx_transient dynChildCore (complementKey true account 0) rfl account (dynPath "temp")
  exact ⟨p.1,t.1,t.2.1⟩

theorem dyn_other_account_preserved :
    dynChildCore.source.world.accounts (⟨2,by decide⟩) = dynCore.source.world.accounts (⟨2,by decide⟩) := by
  rw [dyn_actual_child_sequence,runPackedSlots_other_account _ _ _ (by decide),dyn_actual_caller_sequence]
  exact @runPackedSlots_other_account dynEnv.layout dynEnv.lay dynEnv.lay dynRegistry dynTempRegistry dynCore dynPlans (⟨2,by decide⟩) dyn_caller_other_address

theorem dyn_unrelated_padding_preserved :
    dynChildCore.residual.cells (complementKey false account 44) = dynResidual.cells (complementKey false account 44) := by
  rw [dyn_actual_child_sequence,runPackedSlots_other_complement _ _ _ _ _ (by decide),dyn_actual_caller_sequence]
  exact @runPackedSlots_other_complement dynEnv.layout dynEnv.lay dynEnv.lay dynRegistry dynTempRegistry dynCore dynPlans false account 44 (dyn_caller_other_slot 44 (by decide))

theorem dyn_initial_unknown_tail : dynResidual.cells (complementKey false account 1002) = 77 := by
  have residual : dynStore.2 = packedMask (dynRegistry account) dynSnapshot :=
    packedStoreWriteback_residual _ _ _ _ _ (Option.get_mem dyn_store_ready)
  calc
    _ = packedMask (dynRegistry account) dynSnapshot 1002 :=
      initialPackedComplement_false dynRegistry dynTempRegistry dynSnapshot account 1002
    _ = dynStore.2 1002 := congrFun residual.symm 1002
    _ = 77 := dyn_padding_and_unknown_tail.2.1

theorem dyn_unknown_tail_preserved : dynChildCore.residual.cells (complementKey false account 1002) = 77 := by
  rw [dyn_actual_child_sequence,runPackedSlots_other_complement _ _ _ _ _ (by decide),dyn_actual_caller_sequence,
    @runPackedSlots_other_complement dynEnv.layout dynEnv.lay dynEnv.lay dynRegistry dynTempRegistry dynCore dynPlans false account 1002 (dyn_caller_other_slot 1002 (by decide))]
  exact dyn_initial_unknown_tail

theorem dyn_persistent_transient_path_isolation :
    (dynChildCore.source.world.accounts account).storage.cell (dynPath "temp") = none ∧
    (dynChildCore.source.transient.cells account).cell (dynPath "xs") = none := by
  rw [dyn_actual_child_sequence]
  constructor
  · rw [runPackedSlots_persistent_unselected _ _ _ _ (by decide),dyn_actual_caller_sequence,
      @runPackedSlots_persistent_unselected dynEnv.layout dynEnv.lay dynEnv.lay dynRegistry dynTempRegistry dynCore dynPlans account (dynPath "temp") dyn_registry_no_temp]
    rfl
  · rw [runPackedSlots_transient_unselected _ _ _ _ (by decide),dyn_actual_caller_sequence,
      @runPackedSlots_transient_unselected dynEnv.layout dynEnv.lay dynEnv.lay dynRegistry dynTempRegistry dynCore dynPlans account (dynPath "xs") dyn_temp_registry_no_xs]
    rfl

end Solidity.Yul.Views.Controls
