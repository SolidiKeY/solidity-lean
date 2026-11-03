import Solidity.Yul.Views.DeclarationControls

namespace Solidity.Yul.Views.Controls

def declChildRequest : PackedSlotRequest := ⟨false,account,0,packedRawB⟩
def declTransientRequest : PackedSlotRequest := ⟨true,account,0,packedRawB⟩
theorem decl_child_ready : (preparePackedSlot declPackingRegistry declPackingRegistry declChildRequest).isSome := by decide
theorem decl_transient_ready : (preparePackedSlot declPackingRegistry declPackingRegistry declTransientRequest).isSome := by decide
def declChildPlan := (preparePackedSlot declPackingRegistry declPackingRegistry declChildRequest).get decl_child_ready
def declTransientPlan := (preparePackedSlot declPackingRegistry declPackingRegistry declTransientRequest).get decl_transient_ready

def declInitialCore : ResidualCompanion declPackingEnv.layout declPackingEnv.lay declPackingEnv.lay complementCarrierOwnership :=
  ⟨declPackingState.2.ex,declPackingResidual⟩
def declCallerCore := applyPackedSlot declInitialCore declPackingPlan
def declChildCore := runPackedSlots declCallerCore [declChildPlan,declTransientPlan]

theorem decl_source_unselected_and_isolated :
    (declChildCore.source.world.accounts account).storage.cell (declarationFieldPath declPackingRoot 4) = none ∧
    (declChildCore.source.world.accounts (⟨2,by decide⟩)).storage.cell (declarationFieldPath declPackingRoot 0) = none ∧
    (declChildCore.source.transient.cells account).cell (declarationFieldPath declPackingRoot 0) = none ∧
    (declChildCore.source.world.accounts account).storage.cell (declarationFieldPath declPackingRoot 0) = some (.bool false) := ⟨rfl,rfl,rfl,rfl⟩

theorem decl_nonzero_padding :
    lowByte (declCallerCore.residual.cells (complementKey false account 0)) ⟨26,by decide⟩ = 0xa5 ∧
    lowByte (declChildCore.residual.cells (complementKey false account 0)) ⟨31,by decide⟩ = 0x5a ∧
    lowByte (declChildCore.residual.cells (complementKey true account 0)) ⟨31,by decide⟩ = 0x5a ∧
    lowByte (declChildCore.residual.cells (complementKey false ⟨2,by decide⟩ 0)) ⟨31,by decide⟩ = 0xa5 := by decide

theorem decl_child_reencoding :
    reencodePersistentSlot declPackingRegistry declChildCore account 0 = some packedRawB ∧
    reencodeTransientSlot declPackingRegistry declChildCore account 0 = some packedRawB :=
  ⟨packedPersistent_reencode _ declChildPlan rfl (decl_packing_separated _),
    packedTransient_reencode _ declTransientPlan rfl (decl_packing_separated _)⟩

theorem decl_caller_prefix_rollback :
    companionRollback (companionEnter declCallerCore account account 0 [] false) declChildCore = declCallerCore :=
  packed_frame_child_rollback declInitialCore [declPackingPlan] [declChildPlan,declTransientPlan] account account 0 [] false

theorem decl_committed_child_outer_rollback :
    companionRollback (companionEnter declInitialCore account account 0 [] false)
      (companionCommit (companionEnter declCallerCore account account 0 [] false) declChildCore) = declInitialCore :=
  packed_frame_outer_commit declInitialCore [declPackingPlan] [declChildPlan,declTransientPlan] account account 0 [] false

theorem decl_reset :
    (companionEndTx declChildCore).source.world = declChildCore.source.world ∧
    ((companionEndTx declChildCore).source.transient.cells account).read (declarationFieldPath declPackingRoot 0) = some (.bool false) ∧
    (companionEndTx declChildCore).residual.cells (complementKey true account 0) = 0 := ⟨rfl,rfl,rfl⟩

theorem decl_static_refusal (F : Source.Fr) (s : Source.EMState declPackingEnv [])
    (r : ResidualJournal complementCarrierOwnership) (static : F.static = true) :
    packedSourceStep F declPackingPlan s r = ((.error (.revert []),s),r) := packedSourceStep_static _ _ _ _ static

/-- Pure preparation identity is distinct from journaled/static source effects. -/
theorem decl_unchanged_administrative (s : Source.Storage declPackingEnv.layout (declPackingEnv.lay account))
    (m : SlotView) (view : finiteView (declPackingRegistry account) s m) :
    finiteWriteback (declPackingRegistry account) m s = some s := finiteWriteback_unchanged _ _ _ view

theorem decl_unchanged_empty_and_written_default :
    finiteWriteback [((declPackingRegistry account).get ⟨0,by decide⟩)] (fun _ => packedZeroRaw)
      (Source.Storage.empty (D := declPackingEnv.layout) (L := declPackingEnv.lay account)) = some Source.Storage.empty := by
  rfl

end Solidity.Yul.Views.Controls
