import Solidity.Yul.Views.OwnershipControls

namespace Solidity.Yul.Views.Controls

def otRaw00 := saveSlot (saveSlot dynSnapshot 43 0) 45 0
def otRaw30 := saveSlot otRaw00 43 3
def otRaw31 := saveSlot otRaw30 45 1

theorem ot_shrink_x_fresh : prepareOwnership? packedStepFrame dynComputed dynTestFixed 43 0 dynSnapshotRun.2 otResidual = some otShrinkX := otShrinkX.prepare_eq

theorem ot_shrink_y_ready : (otShrinkX.following? rfl 45 0).isSome := by
  apply otShrinkX.following_ready rfl
  · rw [show otShrinkX.nextRaw = saveSlot dynSnapshot 43 0 from congrArg (fun m => saveSlot m 43 0) ot_initial_raw]; decide
  · rw [show otShrinkX.nextRaw = saveSlot dynSnapshot 43 0 from congrArg (fun m => saveSlot m 43 0) ot_initial_raw]; decide

@[irreducible]
def otShrinkY : OwnershipPlan packedStepFrame dynComputed dynTestFixed 45 0 otShrinkX.step.1.2 otShrinkX.step.2 :=
  (otShrinkX.following? rfl 45 0).get ot_shrink_y_ready

theorem ot_shrink_y_next : otShrinkY.nextRaw = otRaw00 := by
  have same := otShrinkX.following_raw otShrinkY rfl
  exact (congrArg (fun m => saveSlot m 45 0) same).trans (congrArg (fun m => saveSlot (saveSlot m 43 0) 45 0) ot_initial_raw)

theorem ot_shrink_y_map : finiteEncode otShrinkY.next (otShrinkY.step.1.2.2.ex.world.accounts account).storage
    (fun q => otShrinkY.step.2.cells (complementKey false account q)) = some otRaw00 :=
  (otShrinkY.reencode rfl).trans (congrArg some ot_shrink_y_next)

theorem ot_grow_x_ready : (otShrinkY.following? rfl 43 3).isSome := by
  apply otShrinkY.following_ready rfl
  · rw [ot_shrink_y_next]; decide
  · rw [ot_shrink_y_next]; decide

@[irreducible]
def otGrowX : OwnershipPlan packedStepFrame dynComputed dynTestFixed 43 3 otShrinkY.step.1.2 otShrinkY.step.2 :=
  (otShrinkY.following? rfl 43 3).get ot_grow_x_ready

theorem ot_grow_x_next : otGrowX.nextRaw = otRaw30 := by
  have same := otShrinkY.following_raw otGrowX rfl
  exact (congrArg (fun m => saveSlot m 43 3) same).trans (congrArg (fun m => saveSlot m 43 3) ot_shrink_y_next)

theorem ot_grow_x_map : finiteEncode otGrowX.next (otGrowX.step.1.2.2.ex.world.accounts account).storage
    (fun q => otGrowX.step.2.cells (complementKey false account q)) = some otRaw30 :=
  (otGrowX.reencode rfl).trans (congrArg some ot_grow_x_next)

theorem ot_grow_y_ready : (otGrowX.following? rfl 45 1).isSome := by
  apply otGrowX.following_ready rfl
  · rw [ot_grow_x_next]; decide
  · rw [ot_grow_x_next]; decide

@[irreducible]
def otGrowY : OwnershipPlan packedStepFrame dynComputed dynTestFixed 45 1 otGrowX.step.1.2 otGrowX.step.2 :=
  (otGrowX.following? rfl 45 1).get ot_grow_y_ready

theorem ot_grow_y_next : otGrowY.nextRaw = otRaw31 := by
  have same := otGrowX.following_raw otGrowY rfl
  exact (congrArg (fun m => saveSlot m 45 1) same).trans (congrArg (fun m => saveSlot m 45 1) ot_grow_x_next)

theorem ot_grow_y_map : finiteEncode otGrowY.next (otGrowY.step.1.2.2.ex.world.accounts account).storage
    (fun q => otGrowY.step.2.cells (complementKey false account q)) = some otRaw31 :=
  (otGrowY.reencode rfl).trans (congrArg some ot_grow_y_next)

theorem ot_lengths_31 :
    (Source.readLen (E := dynEnv) packedStepFrame (dynPath "xs")).run otGrowY.step.1.2 = (.ok 3,otGrowY.step.1.2) ∧
    (Source.readLen (E := dynEnv) packedStepFrame (dynPath "ys")).run otGrowY.step.1.2 = (.ok 1,otGrowY.step.1.2) := by
  constructor
  · have read := otGrowY.readLen rfl dynXTrace
    rw [ot_grow_y_next] at read
    exact read
  · exact otGrowY.header_readLen rfl dynYTrace rfl

theorem ot_real_child_rollback :
    companionRollback (companionEnter otShrinkX.after account account 0 [] false) otShrinkY.after = otShrinkX.after :=
  otShrinkX.child_rollback otShrinkY rfl

theorem ot_real_child_commit_outer_rollback :
    companionRollback (companionEnter otShrinkX.before account account 0 [] false)
      (companionCommit (companionEnter otShrinkX.after account account 0 [] false) otShrinkY.after) = otShrinkX.before :=
  otShrinkX.committed_child_outer_rollback otShrinkY rfl

theorem ot_sequence_every_H (H : Source.HeapTy) (ok : Source.MemOK dynEnv H dynSnapshotRun.2) :
    Source.MemOK dynEnv H otGrowY.step.1.2 :=
  otGrowY.MemOK H (otGrowX.MemOK H (otShrinkY.MemOK H (otShrinkX.MemOK H ok)))

theorem ot_sequence_inhabited_MemOK : Source.MemOK dynEnv dynStorageState.2.heap.ty otGrowY.step.1.2 :=
  ot_sequence_every_H _ dyn_computed_snapshot_inhabited_MemOK

end Solidity.Yul.Views.Controls
