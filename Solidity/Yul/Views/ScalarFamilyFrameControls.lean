import Solidity.Yul.Views.ScalarFamilySequence
import Solidity.Yul.Views.IntDynamicRegions

namespace Solidity.Yul.Views.Controls

theorem sf_initial_MemOK : Source.MemOK sfEnv sfState.2.heap.ty sfState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem sf_regrow_MemOK : Source.MemOK sfEnv sfState.2.heap.ty sfRegrow.step.1.2 := sf_every_H _ sf_initial_MemOK

theorem sf_other_account : sfRegrow.after.source.world.accounts (⟨2,by decide⟩) = sfState.2.ex.world.accounts (⟨2,by decide⟩) :=
  (sfRegrow.account_other _ (by decide)).trans ((sfZero.account_other _ (by decide)).trans
    ((sfShrink.account_other _ (by decide)).trans (sfFill.account_other _ (by decide))))

theorem sf_transient_source_unchanged : sfRegrow.after.source.transient = sfState.2.ex.transient :=
  sfRegrow.transient_unchanged.trans (sfZero.transient_unchanged.trans
    (sfShrink.transient_unchanged.trans sfFill.transient_unchanged))

theorem sf_other_bank (q : Roadmap.Word) : sfRegrow.step.2.cells (complementKey true account q) = sfResidual.cells (complementKey true account q) :=
  (sfRegrow.other_key _ (Or.inl (by change true ≠ false; decide))).trans
    ((sfZero.other_key _ (Or.inl (by change true ≠ false; decide))).trans
      ((sfShrink.other_key _ (Or.inl (by change true ≠ false; decide))).trans
        (sfFill.other_key _ (Or.inl (by change true ≠ false; decide)))))

theorem sf_whole_endTx : finiteEncode sfRegrow.next ((companionEndTx sfRegrow.after).source.world.accounts account).storage
    (fun q => (companionEndTx sfRegrow.after).residual.cells (complementKey false account q)) = some sfRaw34 :=
  (sfRegrow.endTx_reencode rfl).trans (congrArg some sf_regrow_next)

theorem sf_unknown_slot_unchanged : sfRaw34 47 = 77 := rfl

theorem sf_nonzero_padding : sfRaw34 2000 = sfWordBytes := rfl

theorem sf_wrong_root_type : sfEnv.rootTy (sfName "xs") ≠ some (.array .storage sfBytes.ty none) := by decide

theorem sf_wrong_index_shape : sfEnv.cellTy ⟨sfName "xs",[.field 0]⟩ = .tuple [] := rfl

theorem sf_old_selectors_unchanged : sfLayout.headerTrace = [] ∧ sfLayout.unsignedTrace = [] ∧ sfLayout.integerTrace = [] := ⟨rfl,rfl,rfl⟩

end Solidity.Yul.Views.Controls
