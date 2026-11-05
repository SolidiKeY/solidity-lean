import Solidity.Yul.Views.PackedDynamicMaskControls

namespace Solidity.Yul.Views.Controls

theorem pd_initial_MemOK : Source.MemOK pdEnv pdState.2.heap.ty pdState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem pd_regrow_MemOK : Source.MemOK pdEnv pdState.2.heap.ty pdRegrow.step.1.2 := pd_every_H _ pd_initial_MemOK

theorem pd_alias_MemOK : Source.MemOK pdEnv pdState.2.heap.ty pdAliases := by
  have h := pd_regrow_MemOK
  exact ⟨⟨h.1.1,⟨rfl,rfl,trivial⟩⟩,h.2⟩

theorem pd_other_account : pdRegrow.after.source.world.accounts (⟨2,by decide⟩) = pdState.2.ex.world.accounts (⟨2,by decide⟩) :=
  (pdRegrow.account_other _ (by decide)).trans ((pdZero.account_other _ (by decide)).trans
    ((pdShrink.account_other _ (by decide)).trans (pdFill.account_other _ (by decide))))

theorem pd_transient_source_unchanged : pdRegrow.after.source.transient = pdState.2.ex.transient :=
  pdRegrow.transient_unchanged.trans (pdZero.transient_unchanged.trans
    (pdShrink.transient_unchanged.trans pdFill.transient_unchanged))

theorem pd_other_bank (q : Roadmap.Word) : pdRegrow.step.2.cells (complementKey true account q) = pdResidual.cells (complementKey true account q) :=
  (pdRegrow.other_key _ (Or.inl (by change true ≠ false; decide))).trans
    ((pdZero.other_key _ (Or.inl (by change true ≠ false; decide))).trans
      ((pdShrink.other_key _ (Or.inl (by change true ≠ false; decide))).trans
        (pdFill.other_key _ (Or.inl (by change true ≠ false; decide)))))

theorem pd_whole_endTx : finiteEncode pdRegrow.next ((companionEndTx pdRegrow.after).source.world.accounts account).storage
    (fun q => (companionEndTx pdRegrow.after).residual.cells (complementKey false account q)) = some pdRaw18 :=
  (pdRegrow.endTx_reencode rfl).trans (congrArg some pd_regrow_next)

theorem pd_unknown_slot_unchanged : pdRaw18 47 = 77 := rfl

theorem pd_u24_nonzero_padding : pdRaw18 2000 = pdWord24 := rfl

/-- Invalid metadata/cell selection remains unsupported PREPARATION, never a
source or Yul refusal/no-op. The old u256 API does not claim packed data. -/
theorem pd_wrong_root_type : pdEnv.rootTy (pdName "xs") ≠ some (.array .storage (.int pdU24) none) := by decide

theorem pd_wrong_index_shape : pdEnv.cellTy ⟨pdName "xs",[.field 0]⟩ = .tuple [] := rfl

theorem pd_old_and_new_end_same (cursor : Nat) :
    (StorageDeclaration.packedUnsignedArray (E := pdEnv) pdU16 rfl (by decide)).endByte cursor =
      (StorageDeclaration.uintArray (E := pdEnv)).endByte cursor := rfl

end Solidity.Yul.Views.Controls
