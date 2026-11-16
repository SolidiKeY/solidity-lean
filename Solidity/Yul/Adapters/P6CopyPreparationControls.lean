import Solidity.Yul.Adapters.P6CopyPreparation
import Solidity.Yul.Adapters.P6SnapshotCopyControls

/-! Kernel changed-field preparation from an actual explicit codec image. The
logical data, copied word and untouched sibling are proved separately to avoid
normalizing opaque inventory preparation or raising checking limits. -/
namespace Solidity.Yul.Adapters.P6CopyPreparation.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ResidualCopy.Controls

def image := FrameHeap.frameOf (carrier .legacy) UnchangedControls.placement
  UnchangedControls.entries residual (fits .legacy) (room .legacy)
def src : ByteSpan image.capacity :=
  ⟨lenU 128 (by decide),lenU 32 (by decide),Or.inr (by change 160≤512;decide)⟩
def dst : ByteSpan image.capacity :=
  ⟨lenU 160 (by decide),lenU 32 (by decide),Or.inr (by change 192≤512;decide)⟩
def reached := P6ByteMemory.copySnapshot image src dst rfl

private theorem nominal_reads : UnchangedControls.nominal.image.Reads (frameBytes image)
    (UnchangedControls.placement.address 0) := by
  rw [image,FrameHeap.frameOf_bytes]
  exact encodeMixedHeap_reads UnchangedControls.placement UnchangedControls.entries
    (by decide) residual UnchangedControls.nominal List.mem_cons_self

theorem first_word : mload (frameBytes image) 128=(⟨2^256-1,by decide⟩ : Roadmap.Word) :=
  nominal_reads 0 _ (by rfl)

theorem second_word : mload (frameBytes image) 160=32767 :=
  nominal_reads 1 _ (by rfl)

theorem copied_words (i : Fin 2) :
    mload (frameBytes reached) (128+i.val*32)=(⟨2^256-1,by decide⟩ : Roadmap.Word) := by
  have choices : i.val=0 ∨ i.val=1 := by omega
  rcases choices with zero | one
  · have addr : 128+i.val*32=128 := by omega
    rw [addr]
    exact (mload_congr _ _ 128 (fun j => P6ByteMemory.copy_outside image src dst rfl _
      (Or.inl (by have bound:=j.isLt;change 128+j.val<160;omega)))).trans first_word
  · have addr : 128+i.val*32=160 := by omega
    rw [addr]
    exact (copied_word image src dst rfl rfl).trans first_word

def values : Fin 2 → Source.Val NominalMemory.Controls.env.layout (.udvt NominalMemory.Controls.small) :=
  fun _ => .udvt (.int (-1) (by decide))

theorem nominal_prepares : ∃ u,update UnchangedControls.placement UnchangedControls.placement
    UnchangedControls.entries UnchangedControls.nominal (frameBytes reached)=some u := by
  obtain ⟨u,prepared,_⟩ := nominal_update_exists UnchangedControls.placement UnchangedControls.placement
    UnchangedControls.entries 0 NominalMemory.Controls.small (some 2) NominalMemory.Controls.data rfl
    UnchangedControls.nominal.image 2 NominalMemory.Controls.lengthOK (by decide) values
    (frameBytes reached) rfl (by trivial) rfl (fun i => by
      change (values i).word=some (mload (frameBytes reached) (128+i.val*32))
      rw [copied_words];rfl) (by decide)
  exact ⟨u,prepared⟩

theorem sibling_reads : UnchangedControls.bytes.image.Reads (frameBytes reached)
    (UnchangedControls.placement.address 1) := by
  apply MemoryImage.reads_congr _ _ (frameBytes image)
  · intro i hi
    apply P6ByteMemory.copy_outside
    right
    change 160+32≤192+i
    omega
  · rw [image,FrameHeap.frameOf_bytes]
    exact encodeMixedHeap_reads UnchangedControls.placement UnchangedControls.entries (by decide)
      residual UnchangedControls.bytes (List.mem_cons_of_mem _ List.mem_cons_self)

theorem inventory_prepares : ∃ us,updates UnchangedControls.placement UnchangedControls.placement
    UnchangedControls.entries UnchangedControls.entries (frameBytes reached)=some us := by
  obtain ⟨nominal,first⟩ := nominal_prepares
  obtain ⟨bytes,second,_⟩ := update_unchanged UnchangedControls.placement UnchangedControls.placement
    .initial UnchangedControls.entries UnchangedControls.coverage UnchangedControls.bytes (by trivial)
    (frameBytes reached) sibling_reads
  change ∃ us, (do
    let a ← update UnchangedControls.placement UnchangedControls.placement UnchangedControls.entries
      UnchangedControls.nominal (frameBytes reached)
    let b ← update UnchangedControls.placement UnchangedControls.placement UnchangedControls.entries
      UnchangedControls.bytes (frameBytes reached)
    pure [a,b])=some us
  rw [first,second]
  exact ⟨[nominal,bytes],rfl⟩

/-- Actual changed-copy preparation exists in the kernel, without a supplied
output Source result, final view equation or opaque decoder evaluation. -/
theorem changed_prepares : ∃ next,
    (P6SnapshotCopy.applyCopy UnchangedControls.placement UnchangedControls.state
      SnapshotControls.mixedCursor image src dst rfl).2=some next := by
  dsimp only [P6SnapshotCopy.applyCopy]
  rw [snapshotStep_eq]
  obtain ⟨us,prepared⟩ := inventory_prepares
  change ∃ next,Option.map _ (updates UnchangedControls.placement UnchangedControls.placement
    UnchangedControls.entries UnchangedControls.entries (frameBytes reached))=some next
  rw [prepared]
  exact ⟨_,rfl⟩

/-- This witness changes an owned physical field; it is not self-copy identity. -/
theorem changed_word : mload (frameBytes reached) 160≠mload (frameBytes image) 160 := by
  have copied := copied_word image src dst rfl rfl
  change mload (frameBytes reached) 160=mload (frameBytes image) 128 at copied
  rw [copied,first_word,second_word]
  decide

/-- Concrete kernel existence AND complete Source/reencoding closure for the
actual changed copy, without a caller-supplied successful preparation. -/
theorem changed_source_view : ∃ next : Σ s,SnapshotCursor UnchangedControls.placement s,
    writeback UnchangedControls.state UnchangedControls.placement UnchangedControls.placement .initial
        UnchangedControls.entries (frameBytes reached)=some (.ok (),next.1) ∧
      encodeMixedHeap next.2.placement next.2.entries (frameBytes reached)=frameBytes reached ∧
      next.1=withSourceHeap UnchangedControls.state next.1.2.heap ∧
      (∀ H,Source.MemOK NominalMemory.Controls.env H UnchangedControls.state →
        Source.MemOK NominalMemory.Controls.env H next.1) := by
  obtain ⟨next,prepared⟩ := changed_prepares
  have output := P6SnapshotCopy.success UnchangedControls.placement UnchangedControls.state
    SnapshotControls.mixedCursor image src dst rfl next prepared
  exact ⟨next,output.1,output.2.1,output.2.2.1,output.2.2.2.1⟩

/-- info: true -/
#guard_msgs in #eval decide (mload (frameBytes reached) 160=(⟨2^256-1,by decide⟩ : Roadmap.Word) ∧
  mload (frameBytes image) 160=32767 ∧ frameBytes reached 224=7 ∧ frameBytes reached 240=20)

end Solidity.Yul.Adapters.P6CopyPreparation.Controls
