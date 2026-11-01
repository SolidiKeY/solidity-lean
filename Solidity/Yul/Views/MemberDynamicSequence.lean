import Solidity.Yul.Views.MemberDynamicControls

namespace Solidity.Yul.Views.Controls

def mdSignedRaw := saveSlot mdGrowRaw 2 11
theorem mdSigned_ready : (mdGrow.following? rfl 2 11).isSome := by
  apply mdGrow.following_ready rfl
  · rw [md_grow_next]; decide
  · rw [md_grow_next]; decide
@[irreducible]
def mdSigned : MemberOwnershipPlan packedStepFrame mdLayout mdFixed 2 11 mdGrow.step.1.2 mdGrow.step.2 :=
  (mdGrow.following? rfl 2 11).get mdSigned_ready
theorem mdSigned_next : mdSigned.nextRaw = mdSignedRaw :=
  (congrArg (fun m => saveSlot m 2 11) (mdGrow.following_raw mdSigned rfl)).trans (congrArg (fun m => saveSlot m 2 11) md_grow_next)
theorem mdSigned_map : finiteEncode mdSigned.next (mdSigned.step.1.2.2.ex.world.accounts account).storage
    (fun q => mdSigned.step.2.cells (complementKey false account q)) = some mdSignedRaw :=
  (mdSigned.reencode rfl).trans (congrArg some mdSigned_next)

def mdBoolRaw := saveSlot mdSignedRaw 4 3
theorem mdBool_ready : (mdSigned.following? rfl 4 3).isSome := by
  apply mdSigned.following_ready rfl
  · rw [mdSigned_next]; decide
  · rw [mdSigned_next]; decide
@[irreducible]
def mdBool : MemberOwnershipPlan packedStepFrame mdLayout mdFixed 4 3 mdSigned.step.1.2 mdSigned.step.2 :=
  (mdSigned.following? rfl 4 3).get mdBool_ready
theorem mdBool_next : mdBool.nextRaw = mdBoolRaw :=
  (congrArg (fun m => saveSlot m 4 3) (mdSigned.following_raw mdBool rfl)).trans (congrArg (fun m => saveSlot m 4 3) mdSigned_next)
theorem mdBool_map : finiteEncode mdBool.next (mdBool.step.1.2.2.ex.world.accounts account).storage
    (fun q => mdBool.step.2.cells (complementKey false account q)) = some mdBoolRaw :=
  (mdBool.reencode rfl).trans (congrArg some mdBool_next)

def mdZeroXRaw := saveSlot mdBoolRaw 1 0
theorem mdZeroX_ready : (mdBool.following? rfl 1 0).isSome := by
  apply mdBool.following_ready rfl
  · rw [mdBool_next]; decide
  · rw [mdBool_next]; decide
@[irreducible]
def mdZeroX : MemberOwnershipPlan packedStepFrame mdLayout mdFixed 1 0 mdBool.step.1.2 mdBool.step.2 :=
  (mdBool.following? rfl 1 0).get mdZeroX_ready
theorem mdZeroX_next : mdZeroX.nextRaw = mdZeroXRaw :=
  (congrArg (fun m => saveSlot m 1 0) (mdBool.following_raw mdZeroX rfl)).trans (congrArg (fun m => saveSlot m 1 0) mdBool_next)
theorem mdZeroX_map : finiteEncode mdZeroX.next (mdZeroX.step.1.2.2.ex.world.accounts account).storage
    (fun q => mdZeroX.step.2.cells (complementKey false account q)) = some mdZeroXRaw :=
  (mdZeroX.reencode rfl).trans (congrArg some mdZeroX_next)

def mdZeroYRaw := saveSlot mdZeroXRaw 2 0
theorem mdZeroY_ready : (mdZeroX.following? rfl 2 0).isSome := by
  apply mdZeroX.following_ready rfl
  · rw [mdZeroX_next]; decide
  · rw [mdZeroX_next]; decide
@[irreducible]
def mdZeroY : MemberOwnershipPlan packedStepFrame mdLayout mdFixed 2 0 mdZeroX.step.1.2 mdZeroX.step.2 :=
  (mdZeroX.following? rfl 2 0).get mdZeroY_ready
theorem mdZeroY_next : mdZeroY.nextRaw = mdZeroYRaw :=
  (congrArg (fun m => saveSlot m 2 0) (mdZeroX.following_raw mdZeroY rfl)).trans (congrArg (fun m => saveSlot m 2 0) mdZeroX_next)
theorem mdZeroY_map : finiteEncode mdZeroY.next (mdZeroY.step.1.2.2.ex.world.accounts account).storage
    (fun q => mdZeroY.step.2.cells (complementKey false account q)) = some mdZeroYRaw :=
  (mdZeroY.reencode rfl).trans (congrArg some mdZeroY_next)

def mdRegrowXRaw := saveSlot mdZeroYRaw 1 18
theorem mdRegrowX_ready : (mdZeroY.following? rfl 1 18).isSome := by
  apply mdZeroY.following_ready rfl
  · rw [mdZeroY_next]; decide
  · rw [mdZeroY_next]; decide
@[irreducible]
def mdRegrowX : MemberOwnershipPlan packedStepFrame mdLayout mdFixed 1 18 mdZeroY.step.1.2 mdZeroY.step.2 :=
  (mdZeroY.following? rfl 1 18).get mdRegrowX_ready
theorem mdRegrowX_next : mdRegrowX.nextRaw = mdRegrowXRaw :=
  (congrArg (fun m => saveSlot m 1 18) (mdZeroY.following_raw mdRegrowX rfl)).trans (congrArg (fun m => saveSlot m 1 18) mdZeroY_next)
theorem mdRegrowX_map : finiteEncode mdRegrowX.next (mdRegrowX.step.1.2.2.ex.world.accounts account).storage
    (fun q => mdRegrowX.step.2.cells (complementKey false account q)) = some mdRegrowXRaw :=
  (mdRegrowX.reencode rfl).trans (congrArg some mdRegrowX_next)

def mdRegrowYRaw := saveSlot mdRegrowXRaw 2 12
theorem mdRegrowY_ready : (mdRegrowX.following? rfl 2 12).isSome := by
  apply mdRegrowX.following_ready rfl
  · rw [mdRegrowX_next]; decide
  · rw [mdRegrowX_next]; decide
@[irreducible]
def mdRegrowY : MemberOwnershipPlan packedStepFrame mdLayout mdFixed 2 12 mdRegrowX.step.1.2 mdRegrowX.step.2 :=
  (mdRegrowX.following? rfl 2 12).get mdRegrowY_ready
theorem mdRegrowY_next : mdRegrowY.nextRaw = mdRegrowYRaw :=
  (congrArg (fun m => saveSlot m 2 12) (mdRegrowX.following_raw mdRegrowY rfl)).trans (congrArg (fun m => saveSlot m 2 12) mdRegrowX_next)
theorem mdRegrowY_map : finiteEncode mdRegrowY.next (mdRegrowY.step.1.2.2.ex.world.accounts account).storage
    (fun q => mdRegrowY.step.2.cells (complementKey false account q)) = some mdRegrowYRaw :=
  (mdRegrowY.reencode rfl).trans (congrArg some mdRegrowY_next)

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
