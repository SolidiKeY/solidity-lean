import Solidity.Yul.Views.PrimitiveDynamicReadControls

namespace Solidity.Yul.Views.Controls

theorem pc_initial_MemOK : Source.MemOK pcEnv pcState.2.heap.ty pcState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem pc_every_H (H : Source.HeapTy) (ok : Source.MemOK pcEnv H pcState) : Source.MemOK pcEnv H pcRegrow.step.1.2 :=
  pcRegrow.MemOK H (pcZero.MemOK H (pcShrink.MemOK H (pcAddressPlan.MemOK H
    (pcBytesPlan.MemOK H (pcBool.MemOK H (pcWord.MemOK H (pcUnsigned.MemOK H (pcSigned.MemOK H ok))))))))

theorem pc_actual_MemOK : Source.MemOK pcEnv pcState.2.heap.ty pcRegrow.step.1.2 := pc_every_H _ pc_initial_MemOK

theorem pc_whole_persistent_endTx : finiteEncode pcRegrow.next ((companionEndTx pcRegrow.after).source.world.accounts account).storage
    (fun q => (companionEndTx pcRegrow.after).residual.cells (complementKey false account q)) = some pcRegrowRaw :=
  (pcRegrow.endTx_reencode rfl).trans (congrArg some pcregrow_next)

theorem pc_prefix_child_rollback : companionRollback (companionEnter pcSigned.after account account 0 [] false) pcUnsigned.after = pcSigned.after :=
  pcSigned.child_rollback pcUnsigned rfl

theorem pc_committed_child_outer_rollback : companionRollback (companionEnter pcSigned.before account account 0 [] false)
    (companionCommit (companionEnter pcSigned.after account account 0 [] false) pcUnsigned.after) = pcSigned.before :=
  pcSigned.committed_child_outer_rollback pcUnsigned rfl

theorem pc_static_after_prefix : pcUnsigned.asStatic.step = ((.error (.revert []),pcSigned.step.1.2),pcSigned.step.2) := pcUnsigned.static_preserves_both

theorem pc_both_inventory_sizes : (pcLayout.primitiveSnapshot pcFixed pcRegrowRaw).length = 46 := rfl

theorem pc_combined_paths_unique : ((pcLayout.primitiveSnapshot pcFixed pcRegrowRaw).map ScalarPath.path).Nodup :=
  pcLayout.primitive_checked_paths pcFixed pcRegrowRaw (by decide)

end Solidity.Yul.Views.Controls
