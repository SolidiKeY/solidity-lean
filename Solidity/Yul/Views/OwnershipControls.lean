import Solidity.Yul.Views.OwnershipFollowing
import Solidity.Yul.Views.ComputedSnapshotControls

namespace Solidity.Yul.Views.Controls

/-- Same supported 2/1 filled Source cells as the prior canonical control.
Synthetic hash witnesses remain distinct from real compiler/EVM receipts.
Unobserved kernel slots retain the original arbitrary77 seed. -/
def otResidual : ResidualJournal complementCarrierOwnership :=
  ⟨fun k => if k.transient then 0 else packedMask (dynComputed.snapshotInventory dynTestFixed dynSnapshot) dynSnapshot k.slot,[]⟩

theorem ot_initial_view : finiteView (dynComputed.snapshotInventory dynTestFixed dynSnapshot)
    (dynSnapshotRun.2.2.ex.world.accounts account).storage dynSnapshot :=
  dynComputed.applySnapshot_view packedStepFrame dynTestFixed dynSnapshot dynStorageState dynSnapshotRun.2 dyn_source_snapshot_step rfl

theorem ot_shrink_decode : (finiteAccountWrite? (T := dynEnv.lay) account
    (dynComputed.snapshotInventory dynTestFixed (saveSlot dynSnapshot 43 0)) (saveSlot dynSnapshot 43 0)).isSome := by decide

theorem ot_shrink_separated : packedSeparationCheck (dynComputed.snapshotInventory dynTestFixed (saveSlot dynSnapshot 43 0)) = true := by decide

def otShrinkOp : Source.Op dynEnv.layout dynEnv.lay dynEnv.lay :=
  (finiteAccountWrite? account (dynComputed.snapshotInventory dynTestFixed (saveSlot dynSnapshot 43 0)) (saveSlot dynSnapshot 43 0)).get ot_shrink_decode

@[irreducible]
def otShrinkX : OwnershipPlan packedStepFrame dynComputed dynTestFixed 43 0 dynSnapshotRun.2 otResidual :=
  ⟨dynComputed.snapshotInventory dynTestFixed dynSnapshot,
   dynComputed.sourceInventory_view packedStepFrame dynTestFixed dynSnapshotRun.2 dynSnapshot
     (fun c member => ot_initial_view c (dynComputed.snapshot_root_member dynTestFixed dynSnapshot c member)),
   dynSnapshot,dyn_computed_actual_source_whole_raw,
   (by rw [dyn_computed_snapshot_inventory]; exact (packedSeparationCheck_iff _).mpr dyn_registry_separated),
   ot_shrink_separated,otShrinkOp,Option.get_mem ot_shrink_decode⟩

theorem ot_initial_raw : otShrinkX.raw = dynSnapshot := by unfold otShrinkX; rfl

theorem ot_shrink_x_length : (Source.readLen (E := dynEnv) packedStepFrame (dynPath "xs")).run otShrinkX.step.1.2 =
    (.ok 0,otShrinkX.step.1.2) := otShrinkX.header_readLen rfl dynXTrace rfl

theorem ot_shrink_x_map : finiteEncode otShrinkX.next (otShrinkX.step.1.2.2.ex.world.accounts account).storage
    (fun q => otShrinkX.step.2.cells (complementKey false account q)) = some (saveSlot dynSnapshot 43 0) := by
  exact (otShrinkX.reencode rfl).trans (congrArg some (congrArg (fun m => saveSlot m 43 0) ot_initial_raw))

theorem ot_shrink_pure_source_same : dynComputed.snapshotWriteback dynTestFixed otShrinkX.nextRaw
    (dynSnapshotRun.2.2.ex.world.accounts account).storage =
    some ((otShrinkX.step.1.2.2.ex.world.accounts account).storage,fun q => otShrinkX.step.2.cells (complementKey false account q)) :=
  otShrinkX.pure_connection rfl

end Solidity.Yul.Views.Controls
