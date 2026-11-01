import Solidity.Yul.Views.LayoutOriginComposition

namespace Solidity.Yul.Views.Controls

def originChildRaw : Roadmap.Word := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe12,by decide⟩
def originTempRaw : Roadmap.Word := ⟨0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd7788,by decide⟩
theorem origin_child_ready : (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 42 originChildRaw).isSome := by decide
theorem origin_temp_ready : (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame true 0 originTempRaw).isSome := by decide
def originChildPlan := (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 42 originChildRaw).get origin_child_ready
def originTempPlan := (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame true 0 originTempRaw).get origin_temp_ready
def originChildFrame := packedSourceStep packedStepFrame originChildPlan originFrame6.1.2 originFrame6.2
def originTempFrame := packedSourceStep packedStepFrame originTempPlan originChildFrame.1.2 originChildFrame.2

def originChildCore : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership := ⟨originTempFrame.1.2.2.ex,originTempFrame.2⟩
theorem origin_child_sequence : originChildCore = runPackedSlots originCallerCore [originChildPlan,originTempPlan] := by
  have temp := (packedSourceStep_companion packedStepFrame originTempPlan originChildFrame.1.2 originChildFrame.2 rfl).2.2.2.2.2
  have child := (packedSourceStep_companion packedStepFrame originChildPlan originFrame6.1.2 originFrame6.2 rfl).2.2.2.2.2
  change (⟨originChildFrame.1.2.2.ex,originChildFrame.2⟩ : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership) = applyPackedSlot originCallerCore originChildPlan at child
  change originChildCore = applyPackedSlot (applyPackedSlot originCallerCore originChildPlan) originTempPlan
  rw [show originChildCore = _ from temp,child]

theorem origin_child_rollback : companionRollback (companionEnter originCallerCore account account 0 [] false) originChildCore = originCallerCore := by
  rw [origin_child_sequence]
  exact packed_frame_rollback originCallerCore [originChildPlan,originTempPlan] account account 0 [] false

theorem origin_committed_child_outer_rollback :
    companionRollback (companionEnter originInitialCore account account 0 [] false)
      (companionCommit (companionEnter originCallerCore account account 0 [] false) originChildCore) = originInitialCore := by
  rw [origin_child_sequence,origin_actual_sequence]
  exact packed_frame_outer_commit originInitialCore [originPlan0,originPlan1,originPlan2,originPlan3,originPlan4,originPlan5,originPlan6]
    [originChildPlan,originTempPlan] account account 0 [] false

theorem origin_static_actual_error : packedSourceStep {packedStepFrame with static := true} originChildPlan originFrame6.1.2 originFrame6.2 =
    ((.error (.revert []),originFrame6.1.2),originFrame6.2) := packedSourceStep_static _ _ _ _ rfl

theorem origin_actual_banks_raw : reencodePersistentSlot originRegistry originChildCore account 42 = some originChildRaw ∧
    reencodeTransientSlot originTempRegistry originChildCore account 0 = some originTempRaw := by
  rw [origin_child_sequence]
  simp only [runPackedSlots]
  constructor
  · rw [packedTransient_persistent_reencode _ originTempPlan rfl]
    exact packedPersistent_reencode _ originChildPlan rfl originChecked.separated
  · exact packedTransient_reencode _ originTempPlan rfl originTempChecked.separated

theorem origin_child_MemOK (H : Source.HeapTy) (ok : Source.MemOK originEnv H originState) : Source.MemOK originEnv H originTempFrame.1.2 :=
  packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (origin_every_H_MemOK H ok))
theorem origin_child_inhabited_MemOK : Source.MemOK originEnv originState.2.heap.ty originTempFrame.1.2 := origin_child_MemOK _ origin_initial_MemOK

theorem origin_unselected_and_account_isolation :
    (originChildCore.source.world.accounts account).storage.cell (originPath "items") = none ∧
    (originChildCore.source.world.accounts (⟨2,by decide⟩)).storage.cell (originPath "a") = none ∧
    (originChildCore.source.transient.cells account).cell (originPath "a") = none ∧
    (originChildCore.source.world.accounts account).storage.cell (originPath "temp") = none := ⟨rfl,rfl,rfl,rfl⟩

theorem origin_temp_defaults_checked : scalarZeroDefaultCheck (originTempRegistry account) = true := by decide

theorem origin_full_transient_reset (q : Roadmap.Word) : reencodeTransientSlot originTempRegistry (companionEndTx originChildCore) account q = some 0 := by
  apply packedEndTx_transient
  intro c member
  exact scalarZeroDefaultCheck_sound _ origin_temp_defaults_checked c ((selectedSlotPaths_mem _ _ c).mp member).1

theorem origin_persistent_and_transient_reset :
    (companionEndTx originChildCore).source.world = originChildCore.source.world ∧
    ((companionEndTx originChildCore).source.transient.cells account).read (originPath "temp") = some (.int 0 (by decide)) ∧
    (companionEndTx originChildCore).residual.cells (complementKey true account 0) = 0 ∧
    (companionEndTx originChildCore).residual.cells (complementKey false account 42) = originChildCore.residual.cells (complementKey false account 42) := by
  have p := companionEndTx_persistent originChildCore (complementKey false account 42) rfl
  have t := companionEndTx_transient originChildCore (complementKey true account 0) rfl account (originPath "temp")
  exact ⟨p.1,t.1,t.2.1,p.2⟩

theorem origin_repeat_order :
    reencodePersistentSlot originRegistry (runPackedSlots originInitialCore [originPlan0,originChildPlan]) account 42 = some originChildRaw ∧
    reencodePersistentSlot originRegistry (runPackedSlots originInitialCore [originChildPlan,originPlan0]) account 42 = some originRaw0 ∧
    originRaw0 ≠ originChildRaw := ⟨packedPersistent_reencode _ originChildPlan rfl originChecked.separated,
      packedPersistent_reencode _ originPlan0 rfl originChecked.separated,by decide⟩

end Solidity.Yul.Views.Controls
