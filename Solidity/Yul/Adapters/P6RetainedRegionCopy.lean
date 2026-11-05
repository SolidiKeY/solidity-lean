import Solidity.Yul.Adapters.P6ByteFamilyCopy

/-! Header-changing copies within actual retained byte/string allocations.
The physical frame survives preparation None. Original allocation extents,
not current shrunk shapes or free-pointer gaps, guard decoded footprints. -/
namespace Solidity.Yul.Adapters.P6RetainedRegionCopy
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ByteFamilyCopy P6CopySource

/-- Select the existing typed byte/string snapshot constructor. -/
def familySnapshot {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (string : Bool) (m : ByteView) (base : Nat) : InventoryObject p (heapByteType string) := by
  cases string
  · exact snapshotBytes p m base
  · exact snapshotString p m base

/-- Only this selected byte/string decoder is total before its capacity check;
this does not characterize failures of arbitrary whole-inventory preparation. -/
theorem update_none_iff {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (string : Bool) (old : Roadmap.Bytes)
    (found : h.get root=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (bound : old.length<2^256) (m : ByteView) :
    update allocated p es ⟨root,_,heapByteData E.layout string old,found,familyImage p string old bound⟩ m=none ↔
      ¬(MemoryShape.bytes (mload m (p.address root)).val).size≤(allocated.shape root).size := by
  let object := familySnapshot p string m (p.address root)
  have decoder : NominalInventory.decode p es (heapByteType string) m (p.address root)=some object := by
    cases string <;> rfl
  have shape : object.shape=MemoryShape.bytes (mload m (p.address root)).val := by
    cases string <;> simp only [object,familySnapshot,snapshotBytes,snapshotString,readBytes,
      List.length_map,List.length_range]
  unfold update
  dsimp only
  rw [decoder]
  change (if fits : object.shape.size≤(allocated.shape root).size then
    some (OwnedInventoryUpdate.mk
      ⟨root,_,heapByteData E.layout string old,found,familyImage p string old bound⟩ object fits) else none)=none ↔ _
  rw [←shape]
  split
  · rename_i fits
    constructor
    · intro impossible;cases impossible
    · intro no;exact False.elim (no fits)
  · rename_i no
    exact ⟨fun _ => no,fun _ => rfl⟩

/-- Existing selected entry and refreshed inventory drive the actual copy and
preparation. This generic operation makes no byte-only failure classification. -/
def prepareEntry {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    {C : Contract} {Δ : Ctx} (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (entry : MixedHeapEntry p) (μ : FrameMem C Δ) (source destination : ByteSpan μ.capacity)
    (same : source.length=destination.length) : FrameMem C Δ × Option (InventoryRealization allocated) :=
  let reached := P6ByteMemory.copySnapshot μ source destination same
  (reached,(update allocated p es entry (frameBytes reached)).map fun u =>
    realizeInventory allocated p history [u] s.2.heap p history rfl es)

/-- Actual physical copy followed by existing selected canonical preparation.
No Source state is duplicated; realization is indexed by that same actual heap. -/
def prepare {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    {C : Contract} {Δ : Ctx} (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (root : Nat) (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (μ : FrameMem C Δ) (source destination : ByteSpan μ.capacity) (same : source.length=destination.length) :
    FrameMem C Δ × Option (InventoryRealization allocated) :=
  prepareEntry s allocated p history es
    ⟨root,_,heapByteData E.layout string old,found,
      familyImage p string old (heapByte_length_bound s.2.heap p root string old found)⟩
    μ source destination same

/-- Exact computed unsupported preparation while retaining the actual copied
frame; it is not a Source/Yul refusal, no-op, deallocation or cleaning rule. -/
theorem prepare_none_iff {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    {C : Contract} {Δ : Ctx} (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (root : Nat) (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (μ : FrameMem C Δ) (source destination : ByteSpan μ.capacity) (same : source.length=destination.length) :
    (prepare s allocated p history es root string old found μ source destination same).2=none ↔
      ¬(MemoryShape.bytes (mload (frameBytes (P6ByteMemory.copySnapshot μ source destination same))
        (p.address root)).val).size≤(allocated.shape root).size := by
  unfold prepare prepareEntry
  rw [Option.map_eq_none_iff]
  exact update_none_iff allocated p es root string old found _ _

/-- A successful numeric check yields actual selected preparation, Source write
and complete refreshed view. Original-region separation also protects other
current objects after shrink; no dormant tail is discarded or zeroed. -/
theorem region_copy {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (distinct : (es.map MixedHeapEntry.id).Nodup)
    (μ : FrameMem C Δ) (residual : ByteView)
    (initial : frameBytes μ=encodeMixedHeap p es residual)
    (root : Nat) (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (source destination : ByteSpan μ.capacity) (same : source.length=destination.length)
    (inside : destination.length.val.toNat=0 ∨
      p.address root≤destination.offset.val.toNat ∧
      destination.offset.val.toNat+destination.length.val.toNat≤p.address root+(allocated.shape root).size)
    (capacity : (MemoryShape.bytes (mload (frameBytes (P6ByteMemory.copySnapshot μ source destination same))
      (p.address root)).val).size≤(allocated.shape root).size) :
    let reached:=P6ByteMemory.copySnapshot μ source destination same
    let bs:=readBytes (frameBytes reached) (p.address root+32) (mload (frameBytes reached) (p.address root)).val
    ∃ r : InventoryRealization allocated,
      (prepare s allocated p history es root string old found μ source destination same).2=some r ∧
      (Source.heapPut root ⟨heapByteType string,heapByteData E.layout string bs⟩ : Source.EM E Γ Unit).run s=
        (.ok (),withSourceHeap s r.heap) ∧
      encodeMixedHeap r.placement r.entries (frameBytes reached)=frameBytes reached ∧
      CoversMixedHeap r.entries ∧ r.entries.map MixedHeapEntry.id=es.map MixedHeapEntry.id ∧
      (∀ a,a≠root → r.heap.get a=s.2.heap.get a) ∧
      (∀ H : Source.HeapTy,Source.MemOK E H s → Source.MemOK E H (withSourceHeap s r.heap)) ∧
      r.heap.ty=s.2.heap.ty ∧ r.heap.next=s.2.heap.next ∧
      r.placement.address=p.address ∧ r.placement.free=p.free ∧
      r.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bs⟩ := by
  dsimp only
  let reached := P6ByteMemory.copySnapshot μ source destination same
  let n := (mload (frameBytes reached) (p.address root)).val
  let bytes := readBytes (frameBytes reached) (p.address root+32) n
  have length : bytes.length=n := by simp only [bytes,readBytes,List.length_map,List.length_range]
  have present : (s.2.heap.cells root).isSome := by
    change (s.2.heap.get root).isSome=true
    rw [found]
    rfl
  have originPresent : (origin.cells root).isSome := by rw [←history.occupancy root];exact present
  have bound := heapByte_length_bound s.2.heap p root string old found
  have cap : (MemoryShape.bytes bytes.length).size≤(allocated.shape root).size := by rw [length];exact capacity
  obtain ⟨u,prepared,data⟩ := family_update_exists allocated p es root string old found bound bytes (frameBytes reached) length.symm (by rw [length]) cap
  have identity : u.entry.id=root := congrArg MixedHeapEntry.id (update_entry allocated p es _ _ u prepared)
  let r := realizeInventory allocated p history [u] s.2.heap p history rfl es
  have executed : (runInventoryUpdates [u]).run s=(.ok (),withSourceHeap s r.heap) :=
    realizeInventory_run allocated p history [u] s p history rfl es
  have action : (runInventoryUpdates [u]).run s=
      (Source.heapPut root ⟨heapByteType string,heapByteData E.layout string bytes⟩ : Source.EM E Γ Unit).run s := by
    rw [singleton_run]
    exact update_action allocated p es ⟨root,_,heapByteData E.layout string old,found,familyImage p string old bound⟩
      (frameBytes reached) u prepared (heapByteData E.layout string bytes) data s
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
    have originOther : (origin.cells e.id).isSome := by rw [←history.occupancy e.id];exact otherPresent
    have separate := allocated.separate e.id root originOther originPresent different
    rw [←history.addresses] at separate
    have fits := e.image.fits p e.id e.found
    have originalFits := history.fits e.id otherPresent
    have reads : e.image.Reads (frameBytes reached) (p.address e.id) := by
      apply MemoryImage.reads_congr _ _ (frameBytes μ)
      · intro i hi
        rcases inside with empty | contained
        · have zero : source.length.val.toNat=0 := by rw [same];exact empty
          rw [show reached=P6ByteMemory.copySnapshot μ source destination same from rfl,
            P6ByteMemory.copy_empty μ source destination same zero]
        · apply P6ByteMemory.copy_outside
          omega
      · rw [initial]
        exact encodeMixedHeap_reads p es distinct residual e member
    exact e.image.unchanged _ _ reads
  have images := realizeInventory_images allocated p history [u] s.2.heap p history rfl es
    (frameBytes reached) raw before
  refine ⟨r,?_,action.symm.trans executed,?_,realizeInventory_coverage allocated p history [u] _ p history rfl es coverage,
    realizeInventory_ids allocated p history [u] _ p history rfl es,?_,?_,?_,?_,?_,?_,?_⟩
  · unfold prepare prepareEntry
    dsimp only
    rw [prepared]
    rfl
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

  · have direct := heapPutConcrete_run s root (heapByteData E.layout string bytes)
      (heap_ty_of_get s.2.heap root _ _ found)
    have heaps : r.heap=s.2.heap.write root (heapByteData E.layout string bytes)
        (heap_ty_of_get s.2.heap root _ _ found) :=
      congrArg (fun result => result.2.2.heap) (executed.symm.trans (action.trans direct))
    rw [heaps,Source.Heap.write_get]

end Solidity.Yul.Adapters.P6RetainedRegionCopy
