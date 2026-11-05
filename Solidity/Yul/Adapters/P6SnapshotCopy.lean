import Solidity.Yul.Adapters.P6ByteMemory
import Solidity.Yul.Views.InventorySnapshotCursor

/-! Actual P6 snapshot copies into owned as well as residual regions. The reached
frame is retained when canonical preparation is unsupported. Source writes occur
only in the existing successful snapshot preparation; no source refusal, cleaning,
allocator semantics or arbitrary program correspondence is introduced. -/
namespace Solidity.Yul.Adapters.P6SnapshotCopy
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
variable {C : Contract} {Δ : Ctx}

/-- Copy once, then synchronize that exact reached complete image. -/
def applyCopy {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (μ : FrameMem C Δ) (source destination : ByteSpan μ.capacity)
    (same : source.length=destination.length) :
    FrameMem C Δ × Option (Σ next : Source.EMState E Γ,SnapshotCursor allocated next) :=
  let reached := P6ByteMemory.copySnapshot μ source destination same
  (reached,snapshotStep allocated s c (frameBytes reached))

/-- Both outcomes retain the actual frame and its exact old-source snapshot. -/
theorem reached_image {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (μ : FrameMem C Δ) (source destination : ByteSpan μ.capacity)
    (same : source.length=destination.length) :
    frameBytes (applyCopy allocated s c μ source destination same).1=
      Environment.writeBytes (frameBytes μ) destination.offset.val.toNat (snapshot μ source) := by
  rw [frame_snapshot_read]
  exact P6ByteMemory.copy_image μ source destination same

/-- A successful copy preparation runs actual typed writes, reconstructs the
ENTIRE reached map, preserves administrative state and every initial owner typing.
No final view or Source execution equality is supplied by callers. -/
theorem success {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (μ : FrameMem C Δ) (source destination : ByteSpan μ.capacity)
    (same : source.length=destination.length)
    (next : Σ t : Source.EMState E Γ,SnapshotCursor allocated t)
    (prepared : (applyCopy allocated s c μ source destination same).2=some next) :
    writeback s allocated c.placement c.history c.entries
        (frameBytes (applyCopy allocated s c μ source destination same).1)=some (.ok (),next.1) ∧
      encodeMixedHeap next.2.placement next.2.entries
        (frameBytes (applyCopy allocated s c μ source destination same).1)=
        frameBytes (applyCopy allocated s c μ source destination same).1 ∧
      next.1=withSourceHeap s next.1.2.heap ∧
      (∀ H : Source.HeapTy,Source.MemOK E H s → Source.MemOK E H next.1) ∧
      (CoversMixedHeap c.entries → CoversMixedHeap next.2.entries) ∧
      next.2.entries.map MixedHeapEntry.id=c.entries.map MixedHeapEntry.id := by
  have step : snapshotStep allocated s c
      (frameBytes (P6ByteMemory.copySnapshot μ source destination same))=some next := prepared
  have actual := (snapshotStep_source allocated s c _).symm.trans
    (congrArg (Option.map (fun n => ((.ok () : Except Source.Halt Unit),n.1))) step)
  have stable := snapshotStep_preserves allocated s c _ next step
  exact ⟨actual,snapshotStep_reencode allocated s c _ next step,stable.1,
    fun H ok => snapshotStep_MemOK allocated s c _ next step H ok,
    stable.2.2.2.2.2.2,stable.2.2.2.2.2.1⟩

/-- Unsupported decoding does not erase the physically reached frame. -/
theorem unsupported {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (μ : FrameMem C Δ) (source destination : ByteSpan μ.capacity)
    (same : source.length=destination.length)
    (failed : snapshotStep allocated s c
      (frameBytes (P6ByteMemory.copySnapshot μ source destination same))=none) :
    applyCopy allocated s c μ source destination same=
      (P6ByteMemory.copySnapshot μ source destination same,none) := by
  first | (simp only [applyCopy,failed]; done) | rfl

end Solidity.Yul.Adapters.P6SnapshotCopy
