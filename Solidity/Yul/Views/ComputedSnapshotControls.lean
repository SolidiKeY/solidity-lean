import Solidity.Yul.Views.ComputedSnapshotReads
import Solidity.Yul.Views.ComputedDynamicControls

namespace Solidity.Yul.Views.Controls

theorem dyn_source_snapshot_ready : (dynComputed.applySnapshot? packedStepFrame dynTestFixed dynSnapshot dynStorageState).isSome := by decide

def dynSnapshotRun := (dynComputed.applySnapshot? packedStepFrame dynTestFixed dynSnapshot dynStorageState).get dyn_source_snapshot_ready

theorem dyn_source_snapshot_success : dynSnapshotRun.1 = .ok () := rfl

theorem dyn_source_snapshot_step : dynComputed.applySnapshot? packedStepFrame dynTestFixed dynSnapshot dynStorageState =
    some (.ok (),dynSnapshotRun.2) :=
  (Option.get_mem dyn_source_snapshot_ready).trans (congrArg some (Prod.ext dyn_source_snapshot_success rfl))

def dynXTrace : {entry // entry ∈ dynComputed.headerTrace} :=
  ⟨(dynName "xs",1376),by rw [dyn_header_trace]; exact List.mem_cons_self⟩

def dynYTrace : {entry // entry ∈ dynComputed.headerTrace} :=
  ⟨(dynName "ys",1410),by rw [dyn_header_trace]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩

theorem dyn_computed_actual_source_lengths :
    (Source.readLen (E := dynEnv) packedStepFrame (dynPath "xs")).run dynSnapshotRun.2 = (.ok 2,dynSnapshotRun.2) ∧
    (Source.readLen (E := dynEnv) packedStepFrame (dynPath "ys")).run dynSnapshotRun.2 = (.ok 1,dynSnapshotRun.2) :=
  ⟨dynComputed.applySnapshot_readLen packedStepFrame dynTestFixed dynSnapshot dynStorageState _ dyn_source_snapshot_step rfl dynXTrace,
   dynComputed.applySnapshot_readLen packedStepFrame dynTestFixed dynSnapshot dynStorageState _ dyn_source_snapshot_step rfl dynYTrace⟩

theorem dyn_computed_actual_source_whole_raw : finiteEncode (dynComputed.snapshotInventory dynTestFixed dynSnapshot)
    (dynSnapshotRun.2.2.ex.world.accounts account).storage
    (packedMask (dynComputed.snapshotInventory dynTestFixed dynSnapshot) dynSnapshot) = some dynSnapshot :=
  dynComputed.applySnapshot_reencode packedStepFrame dynTestFixed dynSnapshot dynStorageState _ dyn_source_snapshot_step rfl

theorem dyn_computed_actual_all_cells (c : ScalarPath dynEnv.layout (dynEnv.lay account))
    (member : c ∈ dynComputed.snapshotInventory dynTestFixed dynSnapshot) :
    ∃ v, (Source.readCell (E := dynEnv) packedStepFrame c.path).run dynSnapshotRun.2 = (.ok v,dynSnapshotRun.2) ∧
      c.codec.encode v = c.field.findWord (dynSnapshot c.slot) :=
  dynComputed.applySnapshot_readCell packedStepFrame dynTestFixed dynSnapshot dynStorageState _ dyn_source_snapshot_step rfl c member

theorem dyn_computed_snapshot_every_H (H : Source.HeapTy) (ok : Source.MemOK dynEnv H dynStorageState) :
    Source.MemOK dynEnv H dynSnapshotRun.2 :=
  dynComputed.applySnapshot_MemOK packedStepFrame dynTestFixed dynSnapshot dynStorageState dynSnapshotRun (Option.get_mem dyn_source_snapshot_ready) H ok

theorem dyn_computed_snapshot_inhabited_MemOK : Source.MemOK dynEnv dynStorageState.2.heap.ty dynSnapshotRun.2 :=
  dyn_computed_snapshot_every_H _ dyn_initial_MemOK

end Solidity.Yul.Views.Controls
