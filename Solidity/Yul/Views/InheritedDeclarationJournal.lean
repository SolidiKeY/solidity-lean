import Solidity.Yul.Views.InheritedDeclarationComposition

namespace Solidity.Yul.Views.Controls

def diamondChildRaw : Roadmap.Word := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe12,by decide⟩
def diamondTempRaw : Roadmap.Word := ⟨0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd7788,by decide⟩
theorem diamond_child_ready : (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 0 diamondChildRaw).isSome := by decide
theorem diamond_temp_ready : (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame true 0 diamondTempRaw).isSome := by decide
def diamondChildPlan := (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 0 diamondChildRaw).get diamond_child_ready
def diamondTempPlan := (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame true 0 diamondTempRaw).get diamond_temp_ready
def diamondChildFrame := packedSourceStep packedStepFrame diamondChildPlan diamondFrame6.1.2 diamondFrame6.2
def diamondTempFrame := packedSourceStep packedStepFrame diamondTempPlan diamondChildFrame.1.2 diamondChildFrame.2

def diamondChildCore : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership := ⟨diamondTempFrame.1.2.2.ex,diamondTempFrame.2⟩
theorem diamond_child_sequence : diamondChildCore = runPackedSlots diamondCallerCore [diamondChildPlan,diamondTempPlan] := by
  have temp := (packedSourceStep_companion packedStepFrame diamondTempPlan diamondChildFrame.1.2 diamondChildFrame.2 rfl).2.2.2.2.2
  have child := (packedSourceStep_companion packedStepFrame diamondChildPlan diamondFrame6.1.2 diamondFrame6.2 rfl).2.2.2.2.2
  change (⟨diamondChildFrame.1.2.2.ex,diamondChildFrame.2⟩ : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership) = applyPackedSlot diamondCallerCore diamondChildPlan at child
  change diamondChildCore = applyPackedSlot (applyPackedSlot diamondCallerCore diamondChildPlan) diamondTempPlan
  rw [show diamondChildCore = _ from temp,child]

theorem diamond_child_rollback : companionRollback (companionEnter diamondCallerCore account account 0 [] false) diamondChildCore = diamondCallerCore := by
  rw [diamond_child_sequence]
  exact packed_frame_rollback diamondCallerCore [diamondChildPlan,diamondTempPlan] account account 0 [] false

theorem diamond_committed_child_outer_rollback :
    companionRollback (companionEnter diamondInitialCore account account 0 [] false)
      (companionCommit (companionEnter diamondCallerCore account account 0 [] false) diamondChildCore) = diamondInitialCore := by
  rw [diamond_child_sequence,diamond_actual_sequence]
  exact packed_frame_outer_commit diamondInitialCore [diamondPlan0,diamondPlan1,diamondPlan2,diamondPlan3,diamondPlan4,diamondPlan5,diamondPlan6]
    [diamondChildPlan,diamondTempPlan] account account 0 [] false

theorem diamond_static_actual_error : packedSourceStep {packedStepFrame with static := true} diamondChildPlan diamondFrame6.1.2 diamondFrame6.2 =
    ((.error (.revert []),diamondFrame6.1.2),diamondFrame6.2) := packedSourceStep_static _ _ _ _ rfl

theorem diamond_actual_banks_raw : reencodePersistentSlot diamondRegistry diamondChildCore account 0 = some diamondChildRaw ∧
    reencodeTransientSlot diamondTempRegistry diamondChildCore account 0 = some diamondTempRaw := by
  rw [diamond_child_sequence]
  simp only [runPackedSlots]
  constructor
  · rw [packedTransient_persistent_reencode _ diamondTempPlan rfl]
    exact packedPersistent_reencode _ diamondChildPlan rfl diamondChecked.separated
  · exact packedTransient_reencode _ diamondTempPlan rfl diamondTempChecked.separated

theorem diamond_child_MemOK (H : Source.HeapTy) (ok : Source.MemOK diamondEnv H diamondState) : Source.MemOK diamondEnv H diamondTempFrame.1.2 :=
  packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (diamond_every_H_MemOK H ok))
theorem diamond_child_inhabited_MemOK : Source.MemOK diamondEnv diamondState.2.heap.ty diamondTempFrame.1.2 := diamond_child_MemOK _ diamond_initial_MemOK

theorem diamond_unselected_and_account_isolation :
    (diamondChildCore.source.world.accounts account).storage.cell (diamondPath "items") = none ∧
    (diamondChildCore.source.world.accounts (⟨2,by decide⟩)).storage.cell (diamondPath "a") = none ∧
    (diamondChildCore.source.transient.cells account).cell (diamondPath "a") = none ∧
    (diamondChildCore.source.world.accounts account).storage.cell (diamondPath "temp") = none := ⟨rfl,rfl,rfl,rfl⟩

theorem diamond_temp_defaults_checked : scalarZeroDefaultCheck (diamondTempRegistry account) = true := by decide

theorem diamond_full_transient_reset (q : Roadmap.Word) : reencodeTransientSlot diamondTempRegistry (companionEndTx diamondChildCore) account q = some 0 := by
  apply packedEndTx_transient
  intro c member
  exact scalarZeroDefaultCheck_sound _ diamond_temp_defaults_checked c ((selectedSlotPaths_mem _ _ c).mp member).1

theorem diamond_persistent_and_transient_reset :
    (companionEndTx diamondChildCore).source.world = diamondChildCore.source.world ∧
    ((companionEndTx diamondChildCore).source.transient.cells account).read (diamondPath "temp") = some (.int 0 (by decide)) ∧
    (companionEndTx diamondChildCore).residual.cells (complementKey true account 0) = 0 ∧
    (companionEndTx diamondChildCore).residual.cells (complementKey false account 0) = diamondChildCore.residual.cells (complementKey false account 0) := by
  have p := companionEndTx_persistent diamondChildCore (complementKey false account 0) rfl
  have t := companionEndTx_transient diamondChildCore (complementKey true account 0) rfl account (diamondPath "temp")
  exact ⟨p.1,t.1,t.2.1,p.2⟩

theorem diamond_repeat_order :
    reencodePersistentSlot diamondRegistry (runPackedSlots diamondInitialCore [diamondPlan0,diamondChildPlan]) account 0 = some diamondChildRaw ∧
    reencodePersistentSlot diamondRegistry (runPackedSlots diamondInitialCore [diamondChildPlan,diamondPlan0]) account 0 = some diamondRaw0 ∧
    diamondRaw0 ≠ diamondChildRaw := ⟨packedPersistent_reencode _ diamondChildPlan rfl diamondChecked.separated,
      packedPersistent_reencode _ diamondPlan0 rfl diamondChecked.separated,by decide⟩

end Solidity.Yul.Views.Controls
