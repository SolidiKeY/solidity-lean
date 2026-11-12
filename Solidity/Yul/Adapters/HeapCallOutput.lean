import Solidity.Yul.Adapters.FrameHeap
import Solidity.Yul.Adapters.RawPhysicalCallAccess

/-! Whole ordinary Source-heap writeback after actual physical call output in
the computed object complement. Only the returned prefix is written; requested
input/output spans may be larger and are retained for physical accounting.
Placement provenance, owner MemOK and canonical profile support stay explicit.
Object separation alone is not reserved-word safety or invocation adequacy. -/
namespace Solidity.Yul.Adapters.HeapCallOutput
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views
variable {C : Contract} {Δ : Ctx}

/-- The unchanged administrative Source state is derived from complete actual
heap enumeration and canonical readback, not an assumed final inverse/view. -/
theorem residual_unchanged {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (residual : ByteView) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (carrier : FrameMem C Δ) (fits : MemoryAgreement.Fits carrier residual)
    (room : p.free.val≤carrier.highWaterWords*32)
    (input output : ByteSpan (FrameHeap.frameOf carrier p (generatedHeapEntries p) residual fits room).capacity)
    (data : Solidity.Roadmap.Bytes)
    (outside : ∀ e∈generatedHeapEntries p,
      p.address e.id+e.image.span≤output.offset.val.toNat ∨
      output.offset.val.toNat+min output.length.val.toNat data.length≤p.address e.id) :
    let initial := FrameHeap.frameOf carrier p (generatedHeapEntries p) residual fits room
    let reached := RawPhysicalCallAccess.reached initial input output data
    FrameHeap.writeback s allocated p history reached=.ok (some (.ok (),s)) ∧
      frameBytes reached=Environment.writeBytes (encodeMixedHeap p (generatedHeapEntries p) residual)
        output.offset.val.toNat (World.callOutput data output.length.val.toNat) ∧
      reached.st=carrier.st ∧ reached.key=carrier.key := by
  dsimp only
  have image := RawPhysicalCallAccess.image
    (FrameHeap.frameOf carrier p (generatedHeapEntries p) residual fits room) input output data
  rw [RawPhysicalCallOutput.image,FrameHeap.frameOf_bytes] at image
  have touched := P6ByteMemory.touch_carrier
    (RawPhysicalCallOutput.copy (FrameHeap.frameOf carrier p (generatedHeapEntries p) residual fits room) output data)
    (RawPhysicalCallAccess.inputArea _ input output data)
  have copied := RawPhysicalCallOutput.carrier
    (FrameHeap.frameOf carrier p (generatedHeapEntries p) residual fits room) output data
  refine ⟨?_,image,touched.1.trans copied.1,touched.2.trans copied.2⟩
  unfold FrameHeap.writeback
  rw [image]
  apply FrameHeap.residual_bytes_unchanged H s allocated p history residual ok supported
  intro e member
  simpa only [World.callOutput_length] using outside e member
end Solidity.Yul.Adapters.HeapCallOutput
