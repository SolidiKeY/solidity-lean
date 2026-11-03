import Solidity.Yul.Views.NestedDeclarationPreservation

namespace Solidity.Yul.Views.Controls

theorem nested_child_ready : (preparePackedFrame (ps := nestedDeclRegistry) (ts := nestedDeclRegistry)
    packedStepFrame false 6 packedRawB).isSome := by decide

theorem nested_transient_ready : (preparePackedFrame (ps := nestedDeclRegistry) (ts := nestedDeclRegistry)
    packedStepFrame true 4 nestedRaw4).isSome := by decide

def nestedChildPlan := (preparePackedFrame (ps := nestedDeclRegistry) (ts := nestedDeclRegistry)
    packedStepFrame false 6 packedRawB).get nested_child_ready
def nestedTransientPlan := (preparePackedFrame (ps := nestedDeclRegistry) (ts := nestedDeclRegistry)
    packedStepFrame true 4 nestedRaw4).get nested_transient_ready

def nestedChildFrame := packedSourceStep packedStepFrame nestedChildPlan nestedFrame6.1.2 nestedFrame6.2
def nestedTransientFrame := packedSourceStep packedStepFrame nestedTransientPlan nestedChildFrame.1.2 nestedChildFrame.2

def nestedInitialCore : ResidualCompanion declBoundaryEnv.layout declBoundaryEnv.lay declBoundaryEnv.lay complementCarrierOwnership :=
  ⟨nestedDeclState.2.ex,nestedDeclResidual⟩
def nestedCallerCore : ResidualCompanion declBoundaryEnv.layout declBoundaryEnv.lay declBoundaryEnv.lay complementCarrierOwnership :=
  ⟨nestedFrame6.1.2.2.ex,nestedFrame6.2⟩
def nestedChildCore : ResidualCompanion declBoundaryEnv.layout declBoundaryEnv.lay declBoundaryEnv.lay complementCarrierOwnership :=
  ⟨nestedTransientFrame.1.2.2.ex,nestedTransientFrame.2⟩

theorem nested_actual_source_sequence :
    nestedCallerCore = runPackedSlots nestedInitialCore [nestedPlan4,nestedPlan5,nestedPlan6] ∧
    nestedChildCore = runPackedSlots nestedCallerCore [nestedChildPlan,nestedTransientPlan] := ⟨rfl,rfl⟩

theorem nested_actual_child_rollback :
    companionRollback (companionEnter nestedCallerCore account account 0 [] false) nestedChildCore = nestedCallerCore :=
  packed_frame_rollback nestedCallerCore [nestedChildPlan,nestedTransientPlan] account account 0 [] false

theorem nested_actual_outer_rollback :
    companionRollback (companionEnter nestedInitialCore account account 0 [] false)
      (companionCommit (companionEnter nestedCallerCore account account 0 [] false) nestedChildCore) = nestedInitialCore :=
  packed_frame_outer_commit nestedInitialCore [nestedPlan4,nestedPlan5,nestedPlan6]
    [nestedChildPlan,nestedTransientPlan] account account 0 [] false

theorem nested_actual_static_refusal :
    packedSourceStep {packedStepFrame with static := true} nestedChildPlan nestedFrame6.1.2 nestedFrame6.2 =
      ((.error (.revert []),nestedFrame6.1.2),nestedFrame6.2) := packedSourceStep_static _ _ _ _ rfl

theorem nested_current_frame_reencode :
    reencodePersistentSlot nestedDeclRegistry nestedCallerCore account 6 = some nestedRaw6 := by
  apply packedFrameWrite_persistent_reencode packedStepFrame 6 nestedRaw6 nestedFrame5.1.2 nestedFrame5.2 nestedFrame6
  · unfold packedFrameWrite?
    rw [show preparePackedFrame (ps := nestedDeclRegistry) (ts := nestedDeclRegistry) packedStepFrame false 6 nestedRaw6 = some nestedPlan6 from Option.get_mem nested_slot6_ready]
    rfl
  · rfl
  · exact nested_decl_separated _

theorem nested_child_raw_both_banks :
    reencodePersistentSlot nestedDeclRegistry nestedChildCore account 6 = some packedRawB ∧
    reencodeTransientSlot nestedDeclRegistry nestedChildCore account 4 = some nestedRaw4 := by
  rw [nested_actual_source_sequence.2]
  simp only [runPackedSlots]
  constructor
  · rw [packedTransient_persistent_reencode _ nestedTransientPlan rfl]
    exact packedPersistent_reencode _ nestedChildPlan rfl (nested_decl_separated _)
  · exact packedTransient_reencode _ nestedTransientPlan rfl (nested_decl_separated _)

theorem nested_unselected_paths_and_accounts :
    (nestedChildCore.source.world.accounts account).storage.cell (nestedArrayPath declBoundaryRoot 12) = none ∧
    (nestedChildCore.source.world.accounts (⟨2,by decide⟩)).storage.cell (nestedStructPath declBoundaryRoot 0) = none ∧
    (nestedChildCore.source.transient.cells account).cell (nestedStructPath declBoundaryRoot 0) = none ∧
    (nestedChildCore.source.world.accounts account).storage.read (nestedArrayPath declBoundaryRoot 11) = some (.int 12 (by decide)) :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem nested_actual_reset :
    (companionEndTx nestedChildCore).source.world = nestedChildCore.source.world ∧
    ((companionEndTx nestedChildCore).source.transient.cells account).read (nestedArrayPath declBoundaryRoot 0) = some (.int 0 (by decide)) ∧
    (companionEndTx nestedChildCore).residual.cells (complementKey true account 4) = 0 ∧
    (companionEndTx nestedChildCore).residual.cells (complementKey false account 6) = nestedChildCore.residual.cells (complementKey false account 6) :=
  by
    have persistent := companionEndTx_persistent nestedChildCore (complementKey false account 6) rfl
    have transient := companionEndTx_transient nestedChildCore (complementKey true account 4) rfl account (nestedArrayPath declBoundaryRoot 0)
    exact ⟨persistent.1,transient.1,transient.2.1,persistent.2⟩

end Solidity.Yul.Views.Controls
