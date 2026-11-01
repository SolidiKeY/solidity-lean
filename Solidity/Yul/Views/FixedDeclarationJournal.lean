import Solidity.Yul.Views.FixedDeclarationComposition

namespace Solidity.Yul.Views.Controls

def recursiveChildRaw : Roadmap.Word := ⟨0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb333300,by decide⟩
theorem recursive_child_ready : (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry) packedStepFrame false 8 recursiveChildRaw).isSome := by decide
theorem recursive_transient_ready : (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry) packedStepFrame true 13 recursiveRaw13).isSome := by decide
def recursiveChildPlan := (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry) packedStepFrame false 8 recursiveChildRaw).get recursive_child_ready
def recursiveTransientPlan := (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry) packedStepFrame true 13 recursiveRaw13).get recursive_transient_ready

def recursiveChildFrame := packedSourceStep packedStepFrame recursiveChildPlan recursiveFrame13.1.2 recursiveFrame13.2
def recursiveTransientFrame := packedSourceStep packedStepFrame recursiveTransientPlan recursiveChildFrame.1.2 recursiveChildFrame.2

def recursiveChildCore : ResidualCompanion recursiveDeclEnv.layout recursiveDeclEnv.lay recursiveDeclEnv.lay complementCarrierOwnership :=
  ⟨recursiveTransientFrame.1.2.2.ex,recursiveTransientFrame.2⟩

theorem recursive_child_sequence : recursiveChildCore = runPackedSlots recursiveCallerCore [recursiveChildPlan,recursiveTransientPlan] := rfl

theorem recursive_child_rollback :
    companionRollback (companionEnter recursiveCallerCore account account 0 [] false) recursiveChildCore = recursiveCallerCore :=
  packed_frame_rollback recursiveCallerCore [recursiveChildPlan,recursiveTransientPlan] account account 0 [] false

theorem recursive_committed_child_outer_rollback :
    companionRollback (companionEnter recursiveInitialCore account account 0 [] false)
      (companionCommit (companionEnter recursiveCallerCore account account 0 [] false) recursiveChildCore) = recursiveInitialCore :=
  packed_frame_outer_commit recursiveInitialCore
    [recursivePlan8,recursivePlan9,recursivePlan10,recursivePlan11,recursivePlan12,recursivePlan13]
    [recursiveChildPlan,recursiveTransientPlan] account account 0 [] false

theorem recursive_static_source_error :
    packedSourceStep {packedStepFrame with static := true} recursiveChildPlan recursiveFrame13.1.2 recursiveFrame13.2 =
      ((.error (.revert []),recursiveFrame13.1.2),recursiveFrame13.2) := packedSourceStep_static _ _ _ _ rfl

theorem recursive_child_banks_reencode :
    reencodePersistentSlot recursiveRegistry recursiveChildCore account 8 = some recursiveChildRaw ∧
    reencodeTransientSlot recursiveRegistry recursiveChildCore account 13 = some recursiveRaw13 := by
  rw [recursive_child_sequence]
  simp only [runPackedSlots]
  constructor
  · rw [packedTransient_persistent_reencode _ recursiveTransientPlan rfl]
    exact packedPersistent_reencode _ recursiveChildPlan rfl recursive_separated
  · exact packedTransient_reencode _ recursiveTransientPlan rfl recursive_separated

theorem recursive_unrelated_paths_accounts_banks :
    (recursiveChildCore.source.world.accounts account).storage.cell (recursiveGridPath 2 0 0) = none ∧
    (recursiveChildCore.source.world.accounts (⟨2,by decide⟩)).storage.cell (recursiveGridPath 0 0 0) = none ∧
    (recursiveChildCore.source.transient.cells account).cell (recursiveGridPath 0 0 0) = none ∧
    (recursiveChildCore.source.world.accounts account).storage.read (recursiveValuePath 2) = some (.int 3 (by decide)) :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem recursive_child_every_H_MemOK (H : Source.HeapTy) (ok : Source.MemOK recursiveDeclEnv H recursiveState) :
    Source.MemOK recursiveDeclEnv H recursiveTransientFrame.1.2 :=
  packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (recursive_every_H_MemOK H ok))

theorem recursive_child_inhabited_MemOK : Source.MemOK recursiveDeclEnv recursiveState.2.heap.ty recursiveTransientFrame.1.2 :=
  recursive_child_every_H_MemOK _ recursive_initial_MemOK

theorem recursive_actual_reset :
    (companionEndTx recursiveChildCore).source.world = recursiveChildCore.source.world ∧
    ((companionEndTx recursiveChildCore).source.transient.cells account).read (recursiveValuePath 2) = some (.int 0 (by decide)) ∧
    (companionEndTx recursiveChildCore).residual.cells (complementKey true account 13) = 0 ∧
    (companionEndTx recursiveChildCore).residual.cells (complementKey false account 8) = recursiveChildCore.residual.cells (complementKey false account 8) := by
  have persistent := companionEndTx_persistent recursiveChildCore (complementKey false account 8) rfl
  have transient := companionEndTx_transient recursiveChildCore (complementKey true account 13) rfl account (recursiveValuePath 2)
  exact ⟨persistent.1,transient.1,transient.2.1,persistent.2⟩

theorem recursive_all_defaults_checked : scalarZeroDefaultCheck (recursiveRegistry account) = true := by decide

theorem recursive_raw_transient_reset (q : Roadmap.Word) : reencodeTransientSlot recursiveRegistry (companionEndTx recursiveChildCore) account q = some 0 := by
  apply packedEndTx_transient
  intro c member
  exact scalarZeroDefaultCheck_sound _ recursive_all_defaults_checked c ((selectedSlotPaths_mem _ _ c).mp member).1

theorem recursive_repeated_write_orders :
    reencodePersistentSlot recursiveRegistry (runPackedSlots recursiveInitialCore [recursivePlan8,recursiveChildPlan]) account 8 = some recursiveChildRaw ∧
    reencodePersistentSlot recursiveRegistry (runPackedSlots recursiveInitialCore [recursiveChildPlan,recursivePlan8]) account 8 = some recursiveRaw8 ∧
    recursiveChildRaw ≠ recursiveRaw8 :=
  ⟨packedPersistent_reencode _ recursiveChildPlan rfl recursive_separated,
    packedPersistent_reencode _ recursivePlan8 rfl recursive_separated,by decide⟩

end Solidity.Yul.Views.Controls
