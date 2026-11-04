import Solidity.Yul.Adapters.P6ByteCopyPreparation

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
  first | (simp only;done) | skip
  rcases inside with empty | inside
  · have zero : source.length.val.toNat=0 := by rw [same];exact empty
    rw [P6ByteMemory.copy_empty μ source destination same zero]
  · exact P6ByteMemory.copy_outside μ source destination same a (by omega)

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
  dsimp only
  let reached := P6ByteMemory.copySnapshot μ source destination same
  let bytes := readBytes (frameBytes reached) (p.address root+32) old.length
  have length : bytes.length=old.length := by simp only [bytes,readBytes,List.length_map,List.length_range]
  have present : (s.2.heap.cells root).isSome := by
    change (s.2.heap.get root).isSome=true
    rw [found]
    rfl
  have bound := heapByte_length_bound s.2.heap p root false old found
  have shape : p.shape root=MemoryShape.bytes old.length := heapByte_placement_shape s.2.heap p root false old found
  have headerOld : (mload (frameBytes μ) (p.address root)).val=old.length := by
    rw [initial]
    have word := encodeMixedHeap_source_word p es distinct coverage residual root (.bytes .memory)
      (.bytes old) found 0 ⟨old.length,bound⟩ (.bytesLength old bound)
    exact congrArg Fin.val word
  have header : (mload (frameBytes reached) (p.address root)).val=bytes.length := by
    rw [length]
    have sameHeader := mload_congr (frameBytes reached) (frameBytes μ) (p.address root)
      (fun i => payload_outside μ source destination same (p.address root) old.length inside _
        (Or.inl (by have hi:=i.isLt;omega)))
    exact (congrArg Fin.val sameHeader).trans headerOld
  have capacity : (MemoryShape.bytes bytes.length).size≤(allocated.shape root).size := by
    rw [length,←shape]
    exact history.fits root present
  obtain ⟨u,prepared,data⟩ := byte_update_exists allocated p es root (.bytes old) found
    (.bytes old bound) bytes (frameBytes reached) header (by rw [length]) capacity
  have identity : u.entry.id=root := congrArg MixedHeapEntry.id (update_entry allocated p es _ _ u prepared)
  let r := realizeInventory allocated p history [u] s.2.heap p history rfl es
  have executed : (runInventoryUpdates [u]).run s=(.ok (),withSourceHeap s r.heap) :=
    realizeInventory_run allocated p history [u] s p history rfl es
  have action : (runInventoryUpdates [u]).run s=
      (Source.heapPut root ⟨.bytes .memory,Source.Data.bytes bytes⟩ : Source.EM E Γ Unit).run s := by
    rw [singleton_run]
    exact update_action allocated p es ⟨root,_,.bytes old,found,.bytes old bound⟩
      (frameBytes reached) u prepared (.bytes bytes) data s
  have raw : ∀ v ∈ [u],v.object.image.encode (frameBytes reached) (p.address v.entry.id)=frameBytes reached := by
    intro v member
    have equal := List.mem_singleton.mp member
    subst v
    exact update_raw allocated p es _ _ u prepared
  have before : ∀ e ∈ es,(∀ v ∈ [u],e.id≠v.entry.id) →
      e.image.encode (frameBytes reached) (p.address e.id)=frameBytes reached := by
    intro e member outside
    have different : e.id≠root := by
      rw [←identity]
      exact outside u List.mem_cons_self
    have otherPresent : (s.2.heap.cells e.id).isSome := by
      change (s.2.heap.get e.id).isSome=true
      rw [e.found]
      rfl
    have separate := p.separate e.id root otherPresent present different
    have fits := e.image.fits p e.id e.found
    have live := byte_shape_live_bound old.length
    rw [shape] at separate
    have reads : e.image.Reads (frameBytes reached) (p.address e.id) := by
      apply MemoryImage.reads_congr _ _ (frameBytes μ)
      · intro i hi
        apply payload_outside μ source destination same (p.address root) old.length inside
        omega
      · rw [initial]
        exact encodeMixedHeap_reads p es distinct residual e member
    exact e.image.unchanged _ _ reads
  have images := realizeInventory_images allocated p history [u] s.2.heap p history rfl es
    (frameBytes reached) raw before
  refine ⟨r,action.symm.trans executed,?_,realizeInventory_coverage allocated p history [u] _ p history rfl es coverage,
    realizeInventory_ids allocated p history [u] _ p history rfl es,?_,?_,?_,?_,?_,?_⟩
  · apply encodeMixedHeap_unchanged
    intro e member
    have reads := e.image.encode_reads (frameBytes reached) (r.placement.address e.id)
    rw [images e member] at reads
    exact reads
  · intro a different
    exact (realizeInventory_other allocated p history [u] _ p history rfl es a (by
      intro v member
      have equal := List.mem_singleton.mp member
      subst v
      rw [identity]
      exact different)).1
  · intro H ok
    have safe := runInventoryUpdates_MemOK [u] H s (fun v _ => v.object.image.dataOK) ok
    rw [executed] at safe
    exact safe
  · exact realizeInventory_types allocated p history [u] _ p history rfl es
  · exact (realizeInventory_choices allocated p history [u] _ p history rfl es).2.2
  · exact (realizeInventory_choices allocated p history [u] _ p history rfl es).1
  · exact (realizeInventory_choices allocated p history [u] _ p history rfl es).2.1

end Solidity.Yul.Adapters.P6ByteObjectCopy
