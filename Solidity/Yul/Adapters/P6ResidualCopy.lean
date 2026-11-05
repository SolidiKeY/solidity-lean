import Solidity.Yul.Adapters.P6ByteMemory
import Solidity.Yul.Adapters.FrameHeap
import Solidity.Yul.Views.ResidualMcopy
import Solidity.Yul.Views.NominalInventoryUnchanged

/-! Actual bounded P6 frame copies with the existing residual-copy requests and
canonical Source writeback. Input frame/image equality is an initial relation;
the reached image and Source identity are derived. Capacity room, Word ranges
and access accounting remain distinct. No MCOPY opcode, allocator, gas or
whole-program semantics is added; the P6 side carrier is not Source.EMState. -/
namespace Solidity.Yul.Adapters.P6ResidualCopy
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
variable {C : Contract} {Δ : Ctx}

def sourceSpan {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) (request : ResidualCopyRequest p)
    (room : request.window.size.val=0 ∨ request.source.val+request.window.size.val≤μ.capacity) :
    ByteSpan μ.capacity :=
  ⟨lenU request.source.val request.source.isLt,lenU request.window.size.val request.window.size.isLt,
    by simpa only [lenU,Int.toNat_natCast] using room⟩

def destinationSpan {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) (request : ResidualCopyRequest p)
    (room : request.window.size.val=0 ∨ request.window.destination.val+request.window.size.val≤μ.capacity) :
    ByteSpan μ.capacity :=
  ⟨lenU request.window.destination.val request.window.destination.isLt,
    lenU request.window.size.val request.window.size.isLt,
    by simpa only [lenU,Int.toNat_natCast] using room⟩

/-- Execute the EXISTING snapshot-copy body, including its access accounting. -/
def copyFrame {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) (request : ResidualCopyRequest p)
    (sourceRoom : request.window.size.val=0 ∨ request.source.val+request.window.size.val≤μ.capacity)
    (destinationRoom : request.window.size.val=0 ∨ request.window.destination.val+request.window.size.val≤μ.capacity) :
    FrameMem C Δ :=
  P6ByteMemory.copySnapshot μ (sourceSpan μ request sourceRoom) (destinationSpan μ request destinationRoom) rfl

theorem copy_view {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) (request : ResidualCopyRequest p) (sourceRoom destinationRoom) :
    frameBytes (copyFrame μ request sourceRoom destinationRoom)=
      mcopy (frameBytes μ) request.window.destination.val request.source.val request.window.size.val :=
  P6ByteMemory.copy_view μ (sourceSpan μ request sourceRoom) (destinationSpan μ request destinationRoom) rfl

/-- Overlap reads the OLD complete frame, including owned source payloads. -/
theorem copy_readback {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) (request : ResidualCopyRequest p) (sourceRoom destinationRoom) :
    Environment.readMemory (frameBytes (copyFrame μ request sourceRoom destinationRoom))
      request.window.destination.val request.window.size.val=
      Environment.readMemory (frameBytes μ) request.source.val request.window.size.val := by
  exact (P6ByteMemory.copy_readback μ (sourceSpan μ request sourceRoom)
    (destinationSpan μ request destinationRoom) rfl).trans (frame_snapshot_read μ _)

/-- Empty copies retain the complete frame even for maximum Word offsets. -/
theorem copy_empty {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) (request : ResidualCopyRequest p) (sourceRoom destinationRoom)
    (empty : request.window.size.val=0) : copyFrame μ request sourceRoom destinationRoom=μ :=
  P6ByteMemory.copy_empty μ (sourceSpan μ request sourceRoom) (destinationSpan μ request destinationRoom) rfl empty

/-- Derived full output image; no desired post-write agreement is assumed. -/
theorem copy_image {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) (request : ResidualCopyRequest p) (sourceRoom destinationRoom)
    (residual : ByteView) (initial : frameBytes μ=residualCopyPhysical p residual) :
    frameBytes (copyFrame μ request sourceRoom destinationRoom)=residualCopyPhysical p (request.apply residual) := by
  rw [copy_view,initial]
  exact (request.physical residual).symm

/-- Logical Source identity and exact reserved words after the actual frame
copy. The inventory is computed by the existing request window preparation. -/
theorem source_identity {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (request : ResidualCopyRequest p)
    (supported : ∀ a ty d,s.2.heap.get a=some ⟨ty,d⟩ → TypeSupported E ty)
    (μ : FrameMem C Δ) (sourceRoom destinationRoom) (residual : ByteView)
    (initial : frameBytes μ=residualCopyPhysical p residual) (reserved : ReservedOK residual p.free) :
    writeback s allocated p history (generatedHeapEntries p)
      (frameBytes (copyFrame μ request sourceRoom destinationRoom))=some (.ok (),s) ∧
    ReservedOK (frameBytes (copyFrame μ request sourceRoom destinationRoom)) p.free := by
  first
  | solve | simp only [copy_image μ request sourceRoom destinationRoom residual initial]
  | rw [copy_image μ request sourceRoom destinationRoom residual initial]
    have coverage : CoversMixedHeap (generatedHeapEntries p) := by
      rw [←request.window.inventory.1]
      exact request.window.inventory.2.1
    exact ⟨writeback_encoded s allocated p history _ coverage (generatedHeapEntries_nodup p)
      (fun e _ => supported e.id e.ty e.data e.found) _,
      encodeMixedHeap_reserved p _ _ (request.reserved residual reserved)⟩

/-- The carried intrinsic state/key are separate from logical Source identity. -/
theorem copy_carrier {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) (request : ResidualCopyRequest p) (sourceRoom destinationRoom) :
    (copyFrame μ request sourceRoom destinationRoom).st=μ.st ∧
    (copyFrame μ request sourceRoom destinationRoom).key=μ.key ∧
    (copyFrame μ request sourceRoom destinationRoom).capacity=μ.capacity := by
  have same := P6ByteMemory.copy_carrier μ (sourceSpan μ request sourceRoom) (destinationSpan μ request destinationRoom) rfl
  refine ⟨same.1,same.2,?_⟩
  simp only [copyFrame,P6ByteMemory.copySnapshot,P6ByteMemory.touch_capacity,P6ByteMemory.write_capacity]

/-- Use the REACHED high-water mark, never the generally false old Fits bound. -/
theorem copy_fits {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) (request : ResidualCopyRequest p) (sourceRoom destinationRoom) :
    MemoryAgreement.Fits (copyFrame μ request sourceRoom destinationRoom)
      (frameBytes (copyFrame μ request sourceRoom destinationRoom)) := MemoryAgreement.fits_view _

/-- Exact nonempty access accounting from the actual producer. -/
theorem copy_highWater {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) (request : ResidualCopyRequest p) (sourceRoom destinationRoom)
    (nonempty : request.window.size.val≠0) :
    (copyFrame μ request sourceRoom destinationRoom).highWaterWords=
      max (max μ.highWaterWords ((request.window.destination.val+request.window.size.val+31)/32))
        ((request.source.val+request.window.size.val+31)/32) :=
  P6ByteMemory.copy_highWater μ (sourceSpan μ request sourceRoom) (destinationSpan μ request destinationRoom) rfl nonempty

end Solidity.Yul.Adapters.P6ResidualCopy
