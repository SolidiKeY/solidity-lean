import Solidity.Yul.Views.RecursiveDynamicControls

namespace Solidity.Yul.Views.Controls

def rcSignedRaw := saveSlot rcGrowRaw 3 11
theorem rcSigned_ready : (rcGrow.following? rfl 3 11).isSome := by
  apply rcGrow.following_ready rfl
  · rw [rc_grow_next]; decide
  · rw [rc_grow_next]; decide
@[irreducible]
def rcSigned : RecursiveOwnershipPlan packedStepFrame rcLayout rcFixed 3 11 rcGrow.step.1.2 rcGrow.step.2 :=
  (rcGrow.following? rfl 3 11).get rcSigned_ready
theorem rcSigned_next : rcSigned.nextRaw = rcSignedRaw :=
  (congrArg (fun m => saveSlot m 3 11) (rcGrow.following_raw rcSigned rfl)).trans (congrArg (fun m => saveSlot m 3 11) rc_grow_next)
theorem rcSigned_map : finiteEncode rcSigned.next (rcSigned.step.1.2.2.ex.world.accounts account).storage
    (fun q => rcSigned.step.2.cells (complementKey false account q)) = some rcSignedRaw :=
  (rcSigned.reencode rfl).trans (congrArg some rcSigned_next)

def rcBoolRaw := saveSlot rcSignedRaw 5 3
theorem rcBoolStep_ready : (rcSigned.following? rfl 5 3).isSome := by
  apply rcSigned.following_ready rfl
  · rw [rcSigned_next]; decide
  · rw [rcSigned_next]; decide
@[irreducible]
def rcBool : RecursiveOwnershipPlan packedStepFrame rcLayout rcFixed 5 3 rcSigned.step.1.2 rcSigned.step.2 :=
  (rcSigned.following? rfl 5 3).get rcBoolStep_ready
theorem rcBool_next : rcBool.nextRaw = rcBoolRaw :=
  (congrArg (fun m => saveSlot m 5 3) (rcSigned.following_raw rcBool rfl)).trans (congrArg (fun m => saveSlot m 5 3) rcSigned_next)
theorem rcBool_map : finiteEncode rcBool.next (rcBool.step.1.2.2.ex.world.accounts account).storage
    (fun q => rcBool.step.2.cells (complementKey false account q)) = some rcBoolRaw :=
  (rcBool.reencode rfl).trans (congrArg some rcBool_next)

def rcZeroXRaw := saveSlot rcBoolRaw 2 0
theorem rcZeroX_ready : (rcBool.following? rfl 2 0).isSome := by
  apply rcBool.following_ready rfl
  · rw [rcBool_next]; decide
  · rw [rcBool_next]; decide
@[irreducible]
def rcZeroX : RecursiveOwnershipPlan packedStepFrame rcLayout rcFixed 2 0 rcBool.step.1.2 rcBool.step.2 :=
  (rcBool.following? rfl 2 0).get rcZeroX_ready
theorem rcZeroX_next : rcZeroX.nextRaw = rcZeroXRaw :=
  (congrArg (fun m => saveSlot m 2 0) (rcBool.following_raw rcZeroX rfl)).trans (congrArg (fun m => saveSlot m 2 0) rcBool_next)
theorem rcZeroX_map : finiteEncode rcZeroX.next (rcZeroX.step.1.2.2.ex.world.accounts account).storage
    (fun q => rcZeroX.step.2.cells (complementKey false account q)) = some rcZeroXRaw :=
  (rcZeroX.reencode rfl).trans (congrArg some rcZeroX_next)

def rcZeroYRaw := saveSlot rcZeroXRaw 3 0
theorem rcZeroY_ready : (rcZeroX.following? rfl 3 0).isSome := by
  apply rcZeroX.following_ready rfl
  · rw [rcZeroX_next]; decide
  · rw [rcZeroX_next]; decide
@[irreducible]
def rcZeroY : RecursiveOwnershipPlan packedStepFrame rcLayout rcFixed 3 0 rcZeroX.step.1.2 rcZeroX.step.2 :=
  (rcZeroX.following? rfl 3 0).get rcZeroY_ready
theorem rcZeroY_next : rcZeroY.nextRaw = rcZeroYRaw :=
  (congrArg (fun m => saveSlot m 3 0) (rcZeroX.following_raw rcZeroY rfl)).trans (congrArg (fun m => saveSlot m 3 0) rcZeroX_next)
theorem rcZeroY_map : finiteEncode rcZeroY.next (rcZeroY.step.1.2.2.ex.world.accounts account).storage
    (fun q => rcZeroY.step.2.cells (complementKey false account q)) = some rcZeroYRaw :=
  (rcZeroY.reencode rfl).trans (congrArg some rcZeroY_next)

def rcRegrowXRaw := saveSlot rcZeroYRaw 2 18
theorem rcRegrowX_ready : (rcZeroY.following? rfl 2 18).isSome := by
  apply rcZeroY.following_ready rfl
  · rw [rcZeroY_next]; decide
  · rw [rcZeroY_next]; decide
@[irreducible]
def rcRegrowX : RecursiveOwnershipPlan packedStepFrame rcLayout rcFixed 2 18 rcZeroY.step.1.2 rcZeroY.step.2 :=
  (rcZeroY.following? rfl 2 18).get rcRegrowX_ready
theorem rcRegrowX_next : rcRegrowX.nextRaw = rcRegrowXRaw :=
  (congrArg (fun m => saveSlot m 2 18) (rcZeroY.following_raw rcRegrowX rfl)).trans (congrArg (fun m => saveSlot m 2 18) rcZeroY_next)
theorem rcRegrowX_map : finiteEncode rcRegrowX.next (rcRegrowX.step.1.2.2.ex.world.accounts account).storage
    (fun q => rcRegrowX.step.2.cells (complementKey false account q)) = some rcRegrowXRaw :=
  (rcRegrowX.reencode rfl).trans (congrArg some rcRegrowX_next)

def rcRegrowYRaw := saveSlot rcRegrowXRaw 3 12
theorem rcRegrowY_ready : (rcRegrowX.following? rfl 3 12).isSome := by
  apply rcRegrowX.following_ready rfl
  · rw [rcRegrowX_next]; decide
  · rw [rcRegrowX_next]; decide
@[irreducible]
def rcRegrowY : RecursiveOwnershipPlan packedStepFrame rcLayout rcFixed 3 12 rcRegrowX.step.1.2 rcRegrowX.step.2 :=
  (rcRegrowX.following? rfl 3 12).get rcRegrowY_ready
theorem rcRegrowY_next : rcRegrowY.nextRaw = rcRegrowYRaw :=
  (congrArg (fun m => saveSlot m 3 12) (rcRegrowX.following_raw rcRegrowY rfl)).trans (congrArg (fun m => saveSlot m 3 12) rcRegrowX_next)
theorem rcRegrowY_map : finiteEncode rcRegrowY.next (rcRegrowY.step.1.2.2.ex.world.accounts account).storage
    (fun q => rcRegrowY.step.2.cells (complementKey false account q)) = some rcRegrowYRaw :=
  (rcRegrowY.reencode rfl).trans (congrArg some rcRegrowY_next)

theorem rc_every_H (H : Source.HeapTy) (ok : Source.MemOK rcEnv H rcState) :
    Source.MemOK rcEnv H rcRegrowY.step.1.2 :=
  rcRegrowY.MemOK H (rcRegrowX.MemOK H (rcZeroY.MemOK H (rcZeroX.MemOK H (rcBool.MemOK H (rcSigned.MemOK H (rcGrow.MemOK H ok))))))
theorem rc_written_MemOK : Source.MemOK rcEnv rcState.2.heap.ty rcRegrowY.step.1.2 := rc_every_H _ rc_initial_MemOK

theorem rc_tail_recovered : (rcRegrowYRaw 1001).val % 65536 = 77 ∧
    (rcRegrowYRaw 1001).val / 65536 % 65536 = 32768 ∧
    (rcRegrowYRaw 2001).val % (2^24) = 77 := by decide

theorem rc_caller_prefix_child_rollback :
    companionRollback (companionEnter rcZeroX.after account account 0 [] false) rcZeroY.after = rcZeroX.after :=
  rcZeroX.child_rollback rcZeroY rfl

theorem rc_child_success_outer_rollback :
    companionRollback (companionEnter rcZeroX.before account account 0 [] false)
      (companionCommit (companionEnter rcZeroX.after account account 0 [] false) rcZeroY.after) = rcZeroX.before :=
  rcZeroX.committed_child_outer_rollback rcZeroY rfl

theorem rc_static_prefix : rcRegrowY.asStatic.step = ((.error (.revert []),rcRegrowX.step.1.2),rcRegrowX.step.2) :=
  rcRegrowY.static_preserves_both

theorem rc_persistent_endTx : finiteEncode rcRegrowY.next
    ((companionEndTx rcRegrowY.after).source.world.accounts account).storage
    (fun q => (companionEndTx rcRegrowY.after).residual.cells (complementKey false account q)) = some rcRegrowYRaw :=
  (rcRegrowY.endTx_reencode rfl).trans (congrArg some rcRegrowY_next)

end Solidity.Yul.Views.Controls
