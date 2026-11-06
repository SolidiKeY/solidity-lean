import Solidity.Yul.Views.MemberDynamicSequenceRegrow

-- Serialize concrete proof elaboration to bound pending computed-state memory.
set_option Elab.async false

namespace Solidity.Yul.Views.Controls
theorem md_every_H (H : Source.HeapTy) (ok : Source.MemOK mdEnv H mdState) :
    Source.MemOK mdEnv H mdRegrowY.step.1.2 :=
  mdRegrowY.MemOK H (mdRegrowX.MemOK H (mdZeroY.MemOK H (mdZeroX.MemOK H (mdBool.MemOK H (mdSigned.MemOK H (mdGrow.MemOK H ok))))))
theorem md_written_MemOK : Source.MemOK mdEnv mdState.2.heap.ty mdRegrowY.step.1.2 := md_every_H _ md_initial_MemOK

theorem md_tail_recovered : (mdRegrowYRaw 1001).val % 65536 = 77 ∧
    (mdRegrowYRaw 1001).val / 65536 % 65536 = 0 ∧
    (mdRegrowYRaw 2001).val % (2^24) = 77 := by decide

theorem md_caller_prefix_child_rollback :
    companionRollback (companionEnter mdZeroX.after account account 0 [] false) mdZeroY.after = mdZeroX.after :=
  mdZeroX.child_rollback mdZeroY rfl

theorem md_child_success_outer_rollback :
    companionRollback (companionEnter mdZeroX.before account account 0 [] false)
      (companionCommit (companionEnter mdZeroX.after account account 0 [] false) mdZeroY.after) = mdZeroX.before :=
  mdZeroX.committed_child_outer_rollback mdZeroY rfl

theorem md_static_prefix : mdRegrowY.asStatic.step = ((.error (.revert []),mdRegrowX.step.1.2),mdRegrowX.step.2) :=
  mdRegrowY.static_preserves_both

theorem md_persistent_endTx : finiteEncode mdRegrowY.next
    ((companionEndTx mdRegrowY.after).source.world.accounts account).storage
    (fun q => (companionEndTx mdRegrowY.after).residual.cells (complementKey false account q)) = some mdRegrowYRaw :=
  (mdRegrowY.endTx_reencode rfl).trans (congrArg some mdRegrowY_next)

end Solidity.Yul.Views.Controls
