import Solidity.Yul.Adapters.P6SnapshotCopy
import Solidity.Yul.Adapters.P6ResidualCopyControls
import Solidity.Yul.Views.InventorySnapshotHistoryControls

/-! Actual bounded copies alter an owned nominal signed field, retaining aliases
and unrelated bytes. A noncanonical copied word retains its reached frame with
preparation None. Pipeline labels remain metadata, not external EVM evidence. -/
namespace Solidity.Yul.Adapters.P6SnapshotCopy.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ResidualCopy.Controls

def source (pipeline : Pipeline) : ByteSpan (image pipeline).capacity :=
  ⟨lenU 128 (by decide),lenU 32 (by decide),Or.inr (by change 160≤512;decide)⟩
def destination (pipeline : Pipeline) : ByteSpan (image pipeline).capacity :=
  ⟨lenU 160 (by decide),lenU 32 (by decide),Or.inr (by change 192≤512;decide)⟩
def dirtySource (pipeline : Pipeline) : ByteSpan (image pipeline).capacity :=
  ⟨lenU 224 (by decide),lenU 32 (by decide),Or.inr (by change 256≤512;decide)⟩
def owned (pipeline : Pipeline) := applyCopy UnchangedControls.placement UnchangedControls.state
  SnapshotControls.mixedCursor (image pipeline) (source pipeline) (destination pipeline) rfl
def dirty (pipeline : Pipeline) := applyCopy UnchangedControls.placement UnchangedControls.state
  SnapshotControls.mixedCursor (image pipeline) (dirtySource pipeline) (source pipeline) rfl

/-- info: (true, true) -/
#guard_msgs in #eval ((owned .legacy).2.isSome,(dirty .viaIR).2.isNone)
/-- info: true -/
#guard_msgs in #eval match (owned .legacy).2 with
  | some next => decide
      (NominalMemory.Controls.aliasRead next.1 .here 1=some (⟨2^256-1,by decide⟩ : Roadmap.Word) ∧
       NominalMemory.Controls.aliasRead next.1 (.there .here) 1=some (⟨2^256-1,by decide⟩ : Roadmap.Word) ∧
       (frameBytes (owned .legacy).1 224)=7 ∧ (frameBytes (owned .legacy).1 240)=20 ∧
       mload (frameBytes (owned .legacy).1) 192=3)
  | none => false
/-- info: true -/
#guard_msgs in #eval decide (frameBytes (dirty .viaIR).1 128=7 ∧
  frameBytes (dirty .viaIR).1 130=255 ∧ (dirty .viaIR).1.highWaterWords=8)

/-- The computed complete inventory inhabits the copy/synchronization API.
This kernel witness uses codec laws, not VM evaluation of opaque preparation. -/
theorem self_prepares (pipeline : Pipeline) :
    ∃ next,(applyCopy UnchangedControls.placement UnchangedControls.state
      ⟨UnchangedControls.placement,.initial,generatedHeapEntries UnchangedControls.placement⟩
      (image pipeline) (source pipeline) (source pipeline) rfl).2=some next ∧
      next.1=UnchangedControls.state := by
  dsimp only [applyCopy]
  let cursor : SnapshotCursor UnchangedControls.placement UnchangedControls.state :=
    ⟨UnchangedControls.placement,.initial,generatedHeapEntries UnchangedControls.placement⟩
  have initial := (generated_roundtrip UnchangedControls.state.2.heap.ty UnchangedControls.state
    UnchangedControls.placement UnchangedControls.placement .initial UnchangedControls.actual_MemOK
    UnchangedControls.heap_profile residual).2
  have copied := P6ByteMemory.copy_self_image (image pipeline) (source pipeline)
  have actual : (snapshotStep UnchangedControls.placement UnchangedControls.state cursor
      (frameBytes (P6ByteMemory.copySnapshot (image pipeline) (source pipeline) (source pipeline) rfl))).map
      (fun n => ((.ok () : Except Source.Halt Unit),n.1))=some (.ok (),UnchangedControls.state) := by
    rw [snapshotStep_source,copied,image_bytes]
    exact initial
  obtain ⟨next,prepared,output⟩ := Option.map_eq_some_iff.mp actual
  exact ⟨next,prepared,congrArg Prod.snd output⟩

/-- Actual complete writeback/reencoding/MemOK transport is available for any
successful preparation from this inhabited Source/frame, not only projections. -/
theorem actual_source (pipeline : Pipeline)
    (next : Σ s,SnapshotCursor UnchangedControls.placement s)
    (prepared : (owned pipeline).2=some next) :
    writeback UnchangedControls.state UnchangedControls.placement UnchangedControls.placement .initial
        SnapshotControls.mixedCursor.entries (frameBytes (owned pipeline).1)=some (.ok (),next.1) ∧
      encodeMixedHeap next.2.placement next.2.entries (frameBytes (owned pipeline).1)=
        frameBytes (owned pipeline).1 ∧
      next.1=withSourceHeap UnchangedControls.state next.1.2.heap ∧
      (∀ H,Source.MemOK NominalMemory.Controls.env H UnchangedControls.state →
        Source.MemOK NominalMemory.Controls.env H next.1) ∧
      (CoversMixedHeap SnapshotControls.mixedCursor.entries → CoversMixedHeap next.2.entries) ∧
      next.2.entries.map MixedHeapEntry.id=SnapshotControls.mixedCursor.entries.map MixedHeapEntry.id :=
  success UnchangedControls.placement UnchangedControls.state SnapshotControls.mixedCursor
    (image pipeline) (source pipeline) (destination pipeline) rfl next prepared

end Solidity.Yul.Adapters.P6SnapshotCopy.Controls
