import Solidity.Yul.Views.SignedDynamicMaskControls

namespace Solidity.Yul.Views.Controls

theorem sd_initial_MemOK : Source.MemOK sdEnv sdState.2.heap.ty sdState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem sd_regrow_MemOK : Source.MemOK sdEnv sdState.2.heap.ty sdRegrow.step.1.2 := sd_every_H _ sd_initial_MemOK

theorem sd_alias_MemOK : Source.MemOK sdEnv sdState.2.heap.ty sdAliases := by
  have h := sd_regrow_MemOK
  exact ⟨⟨h.1.1,⟨rfl,rfl,trivial⟩⟩,h.2⟩

theorem sd_other_account : sdRegrow.after.source.world.accounts (⟨2,by decide⟩) = sdState.2.ex.world.accounts (⟨2,by decide⟩) :=
  (sdRegrow.account_other _ (by decide)).trans ((sdZero.account_other _ (by decide)).trans
    ((sdShrink.account_other _ (by decide)).trans (sdFill.account_other _ (by decide))))

theorem sd_transient_source_unchanged : sdRegrow.after.source.transient = sdState.2.ex.transient :=
  sdRegrow.transient_unchanged.trans (sdZero.transient_unchanged.trans
    (sdShrink.transient_unchanged.trans sdFill.transient_unchanged))

theorem sd_other_bank (q : Roadmap.Word) : sdRegrow.step.2.cells (complementKey true account q) = sdResidual.cells (complementKey true account q) :=
  (sdRegrow.other_key _ (Or.inl (by change true ≠ false; decide))).trans
    ((sdZero.other_key _ (Or.inl (by change true ≠ false; decide))).trans
      ((sdShrink.other_key _ (Or.inl (by change true ≠ false; decide))).trans
        (sdFill.other_key _ (Or.inl (by change true ≠ false; decide)))))

theorem sd_whole_endTx : finiteEncode sdRegrow.next ((companionEndTx sdRegrow.after).source.world.accounts account).storage
    (fun q => (companionEndTx sdRegrow.after).residual.cells (complementKey false account q)) = some sdRaw18 :=
  (sdRegrow.endTx_reencode rfl).trans (congrArg some sd_regrow_next)

theorem sd_unknown_slot_unchanged : sdRaw18 47 = 77 := rfl

theorem sd_i24_nonzero_padding : sdRaw18 2000 = sdWord24 := rfl

/-- Invalid metadata/cell selection remains unsupported PREPARATION, never a
source or Yul refusal/no-op. The old u256 API does not claim packed data. -/
theorem sd_wrong_root_type : sdEnv.rootTy (sdName "xs") ≠ some (.array .storage (.int sdI24) none) := by decide

theorem sd_wrong_index_shape : sdEnv.cellTy ⟨sdName "xs",[.field 0]⟩ = .tuple [] := rfl

theorem sd_old_and_new_end_same (cursor : Nat) :
    (StorageDeclaration.signedArray (E := sdEnv) sdI16 rfl).endByte cursor =
      (StorageDeclaration.uintArray (E := sdEnv)).endByte cursor := rfl

end Solidity.Yul.Views.Controls
