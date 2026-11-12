import Solidity.Yul.Adapters.P6CopySource
import Solidity.Yul.Adapters.P6CopyPreparationControls

/-! The actual changed P6 copy reaches a specified whole Source state. Both
nominal aliases observe its new second element; the unrelated byte cell remains
exactly its original typed data. No final Source equality is an input. -/
namespace Solidity.Yul.Adapters.P6CopySource.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6CopyPreparation P6CopyPreparation.Controls

def data : Source.Data NominalMemory.Controls.env.layout NominalMemory.Controls.arrayTy :=
  memberArrayData _ (.udvt NominalMemory.Controls.small) (some 2) 2 NominalMemory.Controls.lengthOK values

def heap := UnchangedControls.state.2.heap.write 0 data
  (heap_ty_of_get UnchangedControls.state.2.heap 0 _ NominalMemory.Controls.data rfl)
def state := withSourceHeap UnchangedControls.state heap

/-- Actual preparation and actual Source operations determine the whole result. -/
theorem exact_source : writeback UnchangedControls.state UnchangedControls.placement
    UnchangedControls.placement .initial UnchangedControls.entries (frameBytes reached)=
      some (.ok (),state) := by
  obtain ⟨u,prepared,newData⟩ := nominal_update_exists UnchangedControls.placement UnchangedControls.placement
    UnchangedControls.entries 0 NominalMemory.Controls.small (some 2) NominalMemory.Controls.data rfl
    UnchangedControls.nominal.image 2 NominalMemory.Controls.lengthOK (by decide) values
    (frameBytes reached) rfl (by trivial) rfl (fun i => by
      change (values i).word=some (mload (frameBytes reached) (128+i.val*32))
      rw [copied_words];rfl) (by decide)
  change update UnchangedControls.placement UnchangedControls.placement UnchangedControls.entries
    UnchangedControls.nominal (frameBytes reached)=some u at prepared
  have first : (Source.heapPut u.entry.id ⟨u.entry.ty,u.object.data⟩ :
      Source.EM NominalMemory.Controls.env _ Unit).run UnchangedControls.state=(.ok (),state) := by
    rw [update_action UnchangedControls.placement UnchangedControls.placement UnchangedControls.entries
      UnchangedControls.nominal (frameBytes reached) u prepared data newData UnchangedControls.state]
    exact heapPutConcrete_run UnchangedControls.state 0 data _
  obtain ⟨v,sibling,found⟩ := update_unchanged UnchangedControls.placement UnchangedControls.placement
    .initial UnchangedControls.entries UnchangedControls.coverage UnchangedControls.bytes (by trivial)
    (frameBytes reached) sibling_reads
  have id : v.entry.id=1 := congrArg MixedHeapEntry.id
    (update_entry UnchangedControls.placement UnchangedControls.placement UnchangedControls.entries
      UnchangedControls.bytes (frameBytes reached) v sibling)
  have still : state.2.heap.get v.entry.id=some ⟨v.entry.ty,v.object.data⟩ := by
    change (UnchangedControls.state.2.heap.write 0 data (by rfl)).get v.entry.id=_
    rw [Source.Heap.write_other _ (by rw [id];decide)]
    exact found
  have second := unchanged_action v state still
  unfold writeback
  change Option.map (fun us => (runInventoryUpdates us).run UnchangedControls.state)
    (do
      let a ← update UnchangedControls.placement UnchangedControls.placement UnchangedControls.entries
        UnchangedControls.nominal (frameBytes reached)
      let b ← update UnchangedControls.placement UnchangedControls.placement UnchangedControls.entries
        UnchangedControls.bytes (frameBytes reached)
      pure [a,b])=_
  rw [prepared,sibling]
  change some ((runInventoryUpdates [u,v]).run UnchangedControls.state)=_
  rw [runInventoryUpdates,Source.Hoare.run_bind]
  rw [first]
  change some ((runInventoryUpdates [v]).run state)=_
  simp only [runInventoryUpdates,Source.Hoare.run_bind]
  rw [second]
  rfl

/-- The synchronized dependent result is this exact state, not only a projection. -/
theorem exact_snapshot : ∃ next,
    (P6SnapshotCopy.applyCopy UnchangedControls.placement UnchangedControls.state
      SnapshotControls.mixedCursor image src dst rfl).2=some next ∧ next.1=state := by
  dsimp only [P6SnapshotCopy.applyCopy]
  have actual := (snapshotStep_source UnchangedControls.placement UnchangedControls.state
    SnapshotControls.mixedCursor (frameBytes reached)).trans exact_source
  obtain ⟨next,prepared,result⟩ := Option.map_eq_some_iff.mp actual
  exact ⟨next,prepared,congrArg Prod.snd result⟩

/-- Exact typed sibling cell, including its old payload, survives. -/
theorem sibling_cell : state.2.heap.get 1=UnchangedControls.state.2.heap.get 1 := by
  change (UnchangedControls.state.2.heap.write 0 data (by rfl)).get 1=_
  exact Source.Heap.write_other _ (by decide) _ _

/-- Every original owner typing is preserved for this exact computed state. -/
theorem every_MemOK (H : Source.HeapTy) (ok : Source.MemOK NominalMemory.Controls.env H UnchangedControls.state) :
    Source.MemOK NominalMemory.Controls.env H state :=
  writeback_MemOK H UnchangedControls.state UnchangedControls.placement UnchangedControls.placement
    .initial UnchangedControls.entries (frameBytes reached) _ exact_source ok

/-- Actual owner indexLoc/readLoc observes the changed shared object through
both typed aliases; retaining the initial Source state would fail this law. -/
theorem aliases :
    NominalMemory.Controls.aliasRead state .here 1=some (⟨2^256-1,by decide⟩ : Roadmap.Word) ∧
    NominalMemory.Controls.aliasRead state (.there .here) 1=some (⟨2^256-1,by decide⟩ : Roadmap.Word) ∧
    NominalMemory.Controls.aliasRead UnchangedControls.state .here 1=some 32767 := by decide

/-- info: (true, true, true) -/
#guard_msgs in #eval (decide (NominalMemory.Controls.aliasRead state .here 1=some (⟨2^256-1,by decide⟩ : Roadmap.Word)),
  decide (NominalMemory.Controls.aliasRead state (.there .here) 1=some (⟨2^256-1,by decide⟩ : Roadmap.Word)),
  decide (NominalMemory.Controls.aliasRead UnchangedControls.state .here 1=some 32767))

end Solidity.Yul.Adapters.P6CopySource.Controls
