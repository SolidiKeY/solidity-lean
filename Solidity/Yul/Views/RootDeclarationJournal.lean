import Solidity.Yul.Views.RootDeclarationComposition

namespace Solidity.Yul.Views.Controls

def rootChildRaw : Roadmap.Word := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe12,by decide⟩
def rootTempRaw : Roadmap.Word := ⟨0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd7788,by decide⟩
theorem root_child_ready : (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 0 rootChildRaw).isSome := by decide
theorem root_temp_ready : (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame true 0 rootTempRaw).isSome := by decide
def rootChildPlan := (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 0 rootChildRaw).get root_child_ready
def rootTempPlan := (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame true 0 rootTempRaw).get root_temp_ready
def rootChildFrame := packedSourceStep packedStepFrame rootChildPlan rootFrame6.1.2 rootFrame6.2
def rootTempFrame := packedSourceStep packedStepFrame rootTempPlan rootChildFrame.1.2 rootChildFrame.2

def rootChildCore : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership := ⟨rootTempFrame.1.2.2.ex,rootTempFrame.2⟩
theorem root_child_sequence : rootChildCore = runPackedSlots rootCallerCore [rootChildPlan,rootTempPlan] := by
  have temp := (packedSourceStep_companion packedStepFrame rootTempPlan rootChildFrame.1.2 rootChildFrame.2 rfl).2.2.2.2.2
  have child := (packedSourceStep_companion packedStepFrame rootChildPlan rootFrame6.1.2 rootFrame6.2 rfl).2.2.2.2.2
  change (⟨rootChildFrame.1.2.2.ex,rootChildFrame.2⟩ : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership) = applyPackedSlot rootCallerCore rootChildPlan at child
  change rootChildCore = applyPackedSlot (applyPackedSlot rootCallerCore rootChildPlan) rootTempPlan
  rw [show rootChildCore = _ from temp,child]

theorem root_child_rollback : companionRollback (companionEnter rootCallerCore account account 0 [] false) rootChildCore = rootCallerCore := by
  rw [root_child_sequence]
  exact packed_frame_rollback rootCallerCore [rootChildPlan,rootTempPlan] account account 0 [] false

theorem root_committed_child_outer_rollback :
    companionRollback (companionEnter rootInitialCore account account 0 [] false)
      (companionCommit (companionEnter rootCallerCore account account 0 [] false) rootChildCore) = rootInitialCore := by
  rw [root_child_sequence,root_actual_sequence]
  exact packed_frame_outer_commit rootInitialCore [rootPlan0,rootPlan1,rootPlan2,rootPlan3,rootPlan4,rootPlan5,rootPlan6]
    [rootChildPlan,rootTempPlan] account account 0 [] false

theorem root_static_actual_error : packedSourceStep {packedStepFrame with static := true} rootChildPlan rootFrame6.1.2 rootFrame6.2 =
    ((.error (.revert []),rootFrame6.1.2),rootFrame6.2) := packedSourceStep_static _ _ _ _ rfl

theorem root_actual_banks_raw : reencodePersistentSlot rootRegistry rootChildCore account 0 = some rootChildRaw ∧
    reencodeTransientSlot rootTempRegistry rootChildCore account 0 = some rootTempRaw := by
  rw [root_child_sequence]
  simp only [runPackedSlots]
  constructor
  · rw [packedTransient_persistent_reencode _ rootTempPlan rfl]
    exact packedPersistent_reencode _ rootChildPlan rfl rootChecked.separated
  · exact packedTransient_reencode _ rootTempPlan rfl rootTempChecked.separated

theorem root_child_MemOK (H : Source.HeapTy) (ok : Source.MemOK rootEnv H rootState) : Source.MemOK rootEnv H rootTempFrame.1.2 :=
  packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (root_every_H_MemOK H ok))
theorem root_child_inhabited_MemOK : Source.MemOK rootEnv rootState.2.heap.ty rootTempFrame.1.2 := root_child_MemOK _ root_initial_MemOK

theorem root_unselected_and_account_isolation :
    (rootChildCore.source.world.accounts account).storage.cell (rootPath "items") = none ∧
    (rootChildCore.source.world.accounts (⟨2,by decide⟩)).storage.cell (rootPath "a") = none ∧
    (rootChildCore.source.transient.cells account).cell (rootPath "a") = none ∧
    (rootChildCore.source.world.accounts account).storage.cell (rootPath "temp") = none := ⟨rfl,rfl,rfl,rfl⟩

theorem root_temp_defaults_checked : scalarZeroDefaultCheck (rootTempRegistry account) = true := by decide

theorem root_full_transient_reset (q : Roadmap.Word) : reencodeTransientSlot rootTempRegistry (companionEndTx rootChildCore) account q = some 0 := by
  apply packedEndTx_transient
  intro c member
  exact scalarZeroDefaultCheck_sound _ root_temp_defaults_checked c ((selectedSlotPaths_mem _ _ c).mp member).1

theorem root_persistent_and_transient_reset :
    (companionEndTx rootChildCore).source.world = rootChildCore.source.world ∧
    ((companionEndTx rootChildCore).source.transient.cells account).read (rootPath "temp") = some (.int 0 (by decide)) ∧
    (companionEndTx rootChildCore).residual.cells (complementKey true account 0) = 0 ∧
    (companionEndTx rootChildCore).residual.cells (complementKey false account 0) = rootChildCore.residual.cells (complementKey false account 0) := by
  have p := companionEndTx_persistent rootChildCore (complementKey false account 0) rfl
  have t := companionEndTx_transient rootChildCore (complementKey true account 0) rfl account (rootPath "temp")
  exact ⟨p.1,t.1,t.2.1,p.2⟩

theorem root_repeat_order :
    reencodePersistentSlot rootRegistry (runPackedSlots rootInitialCore [rootPlan0,rootChildPlan]) account 0 = some rootChildRaw ∧
    reencodePersistentSlot rootRegistry (runPackedSlots rootInitialCore [rootChildPlan,rootPlan0]) account 0 = some rootRaw0 ∧
    rootRaw0 ≠ rootChildRaw := ⟨packedPersistent_reencode _ rootChildPlan rfl rootChecked.separated,
      packedPersistent_reencode _ rootPlan0 rfl rootChecked.separated,by decide⟩

end Solidity.Yul.Views.Controls
