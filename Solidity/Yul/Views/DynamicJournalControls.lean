import Solidity.Yul.Views.DynamicJournalChild

-- Serialize concrete proof elaboration to bound pending computed-state memory.
set_option Elab.async false

namespace Solidity.Yul.Views.Controls
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
