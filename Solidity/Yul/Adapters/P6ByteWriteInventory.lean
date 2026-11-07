import Solidity.Yul.Adapters.P6ByteReferenceWrite

/-! Construct a complete refreshed mixed inventory after an actual memory-byte
write. Canonical decoding, sibling reads and reencoding follow from the existing
mixed image and placement separation. This neither proves general producer
capture nor allocator provenance; retained allocation stays the original one. -/
namespace Solidity.Yul.Adapters.P6ByteWriteInventory
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ByteReferenceWrite P6ByteFamilyCopy P6CopySource

/-- A bounded byte write refreshes the actual Source heap and ALL inventory
images. Padding and unknown bytes remain part of the same supplied raw map. -/
theorem write {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    {C : Contract} {Δ : Ctx} (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (distinct : (es.map MixedHeapEntry.id).Nodup)
    (μ : FrameMem C Δ) (residual : ByteView)
    (initial : frameBytes μ=encodeMixedHeap p es residual)
    (root : Nat) (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (i : Nat) (inside : i<old.length) (b : UInt8)
    (fits : p.address root+32+i+1≤μ.capacity) :
    let reached := P6ByteMemory.store8 μ (payloadOffset p root string old found i inside) (byteWord b) fits
    ∃ r : InventoryRealization allocated,
      (Source.writeLoc F n (.memByte root i)
        (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)).run s=(.ok (),withSourceHeap s r.heap) ∧
      heapByteStateWriteback s p root string old found (frameBytes reached)=some (withSourceHeap s r.heap) ∧
      encodeMixedHeap r.placement r.entries (frameBytes reached)=frameBytes reached ∧
      CoversMixedHeap r.entries ∧ r.entries.map MixedHeapEntry.id=es.map MixedHeapEntry.id ∧
      (∀ a,a≠root → r.heap.get a=s.2.heap.get a) ∧
      (∀ H,Source.MemOK E H s → Source.MemOK E H (withSourceHeap s r.heap)) ∧
      r.heap.get root=some ⟨heapByteType string,heapByteData E.layout string (old.set i b)⟩ ∧
      r.heap.ty=s.2.heap.ty ∧ r.heap.next=s.2.heap.next ∧
      r.placement.address=p.address ∧ r.placement.free=p.free := by
  first | (simp only;done) | skip
  dsimp only
  let reached := P6ByteMemory.store8 μ (payloadOffset p root string old found i inside) (byteWord b) fits
  have entry := mixed_entry p es distinct coverage residual root string old found
  have headerOld : (mload (frameBytes μ) (p.address root)).val=old.length := by rw [initial];exact entry.1
  have payloadOld : readBytes (frameBytes μ) (p.address root+32) old.length=old := by rw [initial];exact entry.2
  have step := P6ByteReferenceWrite.write F n s p root string old found μ headerOld payloadOld i inside b fits
  dsimp only at step
  have physical := store_image μ (payloadOffset p root string old found i inside) b fits
  change frameBytes reached=Environment.writeByte (frameBytes μ) (p.address root+32+i) b at physical
  have header : (mload (frameBytes reached) (p.address root)).val=(old.set i b).length := by
    rw [physical,header_same,List.length_set,headerOld]
  have payload : readBytes (frameBytes reached) (p.address root+32) (old.set i b).length=old.set i b := by
    rw [List.length_set,physical];exact payload_set _ _ _ payloadOld i b
  have present : (s.2.heap.cells root).isSome := by change (s.2.heap.get root).isSome=true;rw [found];rfl
  have bound := heapByte_length_bound s.2.heap p root string old found
  have shape := heapByte_placement_shape s.2.heap p root string old found
  have capacity : (MemoryShape.bytes (old.set i b).length).size≤(allocated.shape root).size := by
    rw [List.length_set,←shape];exact history.fits root present
  obtain ⟨u,prepared,data⟩ := family_update_exists allocated p es root string old found bound
    (old.set i b) (frameBytes reached) header payload capacity
  have identity : u.entry.id=root := congrArg MixedHeapEntry.id (update_entry allocated p es _ _ u prepared)
  let r := realizeInventory allocated p history [u] s.2.heap p history rfl es
  have executed : (runInventoryUpdates [u]).run s=(.ok (),withSourceHeap s r.heap) :=
    realizeInventory_run allocated p history [u] s p history rfl es
  have action : (runInventoryUpdates [u]).run s=
      (Source.heapPut root ⟨heapByteType string,heapByteData E.layout string (old.set i b)⟩ : Source.EM E Γ Unit).run s := by
    rw [singleton_run]
    exact update_action allocated p es ⟨root,_,heapByteData E.layout string old,found,familyImage p string old bound⟩
      (frameBytes reached) u prepared (heapByteData E.layout string (old.set i b)) data s
  have put := heapPutConcrete_run s root (heapByteData E.layout string (old.set i b))
    (heap_ty_of_get s.2.heap root _ _ found)
  have actual : (Source.writeLoc F n (.memByte root i)
      (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)).run s=(.ok (),withSourceHeap s r.heap) :=
    step.1.trans (put.symm.trans (action.symm.trans executed))
  have sameState := congrArg Prod.snd (step.1.symm.trans actual)
  dsimp only at sameState
  have raw : ∀ v ∈ [u],v.object.image.encode (frameBytes reached) (p.address v.entry.id)=frameBytes reached := by
    intro v member
    have equal := List.mem_singleton.mp member
    subst v
    exact update_raw allocated p es _ _ u prepared
  have before : ∀ e ∈ es,(∀ v ∈ [u],e.id≠v.entry.id) →
      e.image.encode (frameBytes reached) (p.address e.id)=frameBytes reached := by
    intro e member outside
    have different : e.id≠root := by rw [←identity];exact outside u List.mem_cons_self
    have otherPresent : (s.2.heap.cells e.id).isSome := by change (s.2.heap.get e.id).isSome=true;rw [e.found];rfl
    have separate := p.separate e.id root otherPresent present different
    have imageFits := e.image.fits p e.id e.found
    have live := byte_shape_live_bound old.length
    rw [shape] at separate
    have reads : e.image.Reads (frameBytes reached) (p.address e.id) := by
      apply MemoryImage.reads_congr _ _ (frameBytes μ)
      · intro j hj
        rw [physical]
        exact if_neg (by omega)
      · rw [initial];exact encodeMixedHeap_reads p es distinct residual e member
    exact e.image.unchanged _ _ reads
  have images := realizeInventory_images allocated p history [u] s.2.heap p history rfl es (frameBytes reached) raw before
  refine ⟨r,actual,?_,?_,realizeInventory_coverage allocated p history [u] _ p history rfl es coverage,
    realizeInventory_ids allocated p history [u] _ p history rfl es,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [←sameState];exact step.2.1
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
      rw [identity];exact different)).1
  · intro H ok
    have safe := runInventoryUpdates_MemOK [u] H s (fun v _ => v.object.image.dataOK) ok
    rw [executed] at safe
    exact safe
  · have heaps := congrArg (fun st : Source.EMState E Γ => st.2.heap) sameState
    dsimp only [withSourceHeap] at heaps
    rw [←heaps]
    exact Source.Heap.write_get _ _ _ _
  · exact realizeInventory_types allocated p history [u] _ p history rfl es
  · exact (realizeInventory_choices allocated p history [u] _ p history rfl es).2.2
  · exact (realizeInventory_choices allocated p history [u] _ p history rfl es).1
  · exact (realizeInventory_choices allocated p history [u] _ p history rfl es).2.1
end Solidity.Yul.Adapters.P6ByteWriteInventory
