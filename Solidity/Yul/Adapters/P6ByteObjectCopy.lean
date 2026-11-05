import Solidity.Yul.Adapters.P6ByteFamilyCopy

/-! General payload-only P6 copy/writeback for actual allocated byte objects.
The real initial encoded heap, placement separation and retained allocation
construct the updated inventory and whole-map reconstruction. This neither
changes byte length nor establishes assembly admission, static-call behavior,
allocator provenance or universal all-type memory adequacy. -/
namespace Solidity.Yul.Adapters.P6ByteObjectCopy
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ByteCopyPreparation P6CopySource

variable {C : Contract} {Δ : Ctx}

/-- No physical byte outside the actual selected payload changes. Empty copies
retain arbitrary offsets without treating them as accesses. -/
theorem payload_outside (μ : FrameMem C Δ) (source destination : ByteSpan μ.capacity)
    (same : source.length=destination.length) (base length : Nat)
    (inside : destination.length.val.toNat=0 ∨
      base+32≤destination.offset.val.toNat ∧
      destination.offset.val.toNat+destination.length.val.toNat≤base+32+length)
    (a : Nat) (outside : a<base+32 ∨ base+32+length≤a) :
    frameBytes (P6ByteMemory.copySnapshot μ source destination same) a=frameBytes μ a := by
  exact P6ByteFamilyCopy.payload_outside μ source destination same base length inside a outside

/-- Exact source action, complete refreshed physical view, coverage/identity and
all original owner typings are derived for ANY byte payload and copy length. -/
theorem payload_copy {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (distinct : (es.map MixedHeapEntry.id).Nodup)
    (μ : FrameMem C Δ) (residual : ByteView)
    (initial : frameBytes μ=encodeMixedHeap p es residual)
    (root : Nat) (old : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨.bytes .memory,Source.Data.bytes old⟩)
    (source destination : ByteSpan μ.capacity) (same : source.length=destination.length)
    (inside : destination.length.val.toNat=0 ∨
      p.address root+32≤destination.offset.val.toNat ∧
      destination.offset.val.toNat+destination.length.val.toNat≤p.address root+32+old.length) :
    let reached:=P6ByteMemory.copySnapshot μ source destination same
    let bs:=readBytes (frameBytes reached) (p.address root+32) old.length
    ∃ r : InventoryRealization allocated,
      (Source.heapPut root ⟨.bytes .memory,Source.Data.bytes bs⟩ : Source.EM E Γ Unit).run s=
        (.ok (),withSourceHeap s r.heap) ∧
      encodeMixedHeap r.placement r.entries (frameBytes reached)=frameBytes reached ∧
      CoversMixedHeap r.entries ∧ r.entries.map MixedHeapEntry.id=es.map MixedHeapEntry.id ∧
      (∀ a,a≠root → r.heap.get a=s.2.heap.get a) ∧
      (∀ H : Source.HeapTy,Source.MemOK E H s → Source.MemOK E H (withSourceHeap s r.heap)) ∧
      r.heap.ty=s.2.heap.ty ∧ r.heap.next=s.2.heap.next ∧
      r.placement.address=p.address ∧ r.placement.free=p.free := by
  exact P6ByteFamilyCopy.payload_copy s allocated p history es coverage distinct μ residual initial
    root false old found source destination same inside

end Solidity.Yul.Adapters.P6ByteObjectCopy
