import Solidity.Yul.Views.HeapAllocationPlacement
import Solidity.Yul.Views.HeapByteMemOK

namespace Solidity.Yul.Views

theorem heapByteType_memory (string : Bool) : (heapByteType string).loc?=some .memory := by
  cases string <;> rfl

def byteAllocatedState {E Γ} (s : Source.EMState E Γ) (string : Bool) (bs : List UInt8) : Source.EMState E Γ :=
  withSourceHeap s (s.2.heap.alloc ⟨heapByteType string,heapByteData E.layout string bs⟩).1

theorem byteAllocRef_run {E Γ} (s : Source.EMState E Γ) (string : Bool) (bs : List UInt8) :
    (Source.allocRef (heapByteData E.layout string bs)).run s=
      (.ok (Source.Val.memRef (heapByteType_memory string) s.2.heap.next),byteAllocatedState s string bs) := by
  cases string <;> rfl

theorem byteAllocRef_MemOK {E Γ} (s : Source.EMState E Γ) (string : Bool) (bs : List UInt8)
    (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (byteAllocatedState s string bs) := by
  have safe := Source.allocRef_mem (H := H) (Γ := Γ) (heapByteData E.layout string bs)
    (heapByteType_memory string) (by cases string <;> trivial) (by cases string <;> trivial)
    s ⟨ok,heapByteData_OK E _ string bs⟩
  rw [byteAllocRef_run] at safe
  exact safe.1

theorem byteAllocRef_RefOK {E Γ} (s : Source.EMState E Γ) (string : Bool) (bs : List UInt8)
    (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    (Source.Val.memRef (heapByteType_memory string) s.2.heap.next).RefOK E (byteAllocatedState s string bs).2.heap.ty := by
  have safe := Source.allocRef_mem (H := H) (Γ := Γ) (heapByteData E.layout string bs)
    (heapByteType_memory string) (by cases string <;> trivial) (by cases string <;> trivial)
    s ⟨ok,heapByteData_OK E _ string bs⟩
  rw [byteAllocRef_run] at safe
  exact safe.2

def byteAllocPlacement {D} (h : Source.Heap D) (p : Placement h) (string : Bool) (bs : List UInt8)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val ≤ base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a ≠ base)
    (fits : base+(MemoryShape.bytes bs.length).size ≤ free.val) :
    Placement (h.alloc ⟨heapByteType string,heapByteData D string bs⟩).1 :=
  heapAllocPlacement h p (heapByteData D string bs) (.bytes bs.length)
    (heapByteData_shape D string bs) base free after fresh fits

/-- Header capacity is derived from the ACTUAL rounded allocation footprint,
not an independent arbitrary decoder/source length restriction. -/
theorem byteAllocation_length_bound (bs : List UInt8) (base : Nat) (free : Roadmap.Word)
    (fits : base+(MemoryShape.bytes bs.length).size ≤ free.val) : bs.length < 2^256 := by
  have live := byte_shape_live_bound bs.length
  have bound := free.isLt
  omega

def byteAllocationView (bs : List UInt8) (base : Nat) (free : Roadmap.Word)
    (fits : base+(MemoryShape.bytes bs.length).size ≤ free.val) (m : ByteView) : ByteView :=
  bytesObjectView bs (byteAllocation_length_bound bs base free fits) (mstore m 64 free) base

theorem byteAllocation_header (bs : List UInt8) (base : Nat) (free : Roadmap.Word)
    (fits : base+(MemoryShape.bytes bs.length).size ≤ free.val) (m : ByteView) :
    (mload (byteAllocationView bs base free fits m) base).val=bs.length :=
  congrArg Fin.val (bytesObject_header bs _ _ base)

theorem byteAllocation_payload (bs : List UInt8) (base : Nat) (free : Roadmap.Word)
    (fits : base+(MemoryShape.bytes bs.length).size ≤ free.val) (m : ByteView) :
    readBytes (byteAllocationView bs base free fits m) (base+32) bs.length=bs :=
  bytesObject_payload_list bs _ _ base

theorem byteAllocation_decode (D : Source.Layout) (string : Bool) (bs : List UInt8)
    (base : Nat) (free : Roadmap.Word) (fits : base+(MemoryShape.bytes bs.length).size ≤ free.val) (m : ByteView) :
    decodeHeapByte D string (byteAllocationView bs base free fits m) base=heapByteData D string bs :=
  decodeHeapByte_encode D string bs _ _ base

theorem byteAllocation_reserved (bs : List UInt8) (base : Nat) (free old : Roadmap.Word)
    (fits : base+(MemoryShape.bytes bs.length).size ≤ free.val) (m : ByteView)
    (start : 128 ≤ base) (reserved : ReservedOK m old) :
    ReservedOK (byteAllocationView bs base free fits m) free := by
  apply bytesObject_reserved bs _ _ base free start
  constructor
  · exact congrArg Fin.val (mload_mstore m 64 free)
  · intro i
    rw [mstore_outside m 64 (96+i.val) free (by omega)]
    exact reserved.2 i

theorem byteAllocation_residual (bs : List UInt8) (base : Nat) (free : Roadmap.Word)
    (fits : base+(MemoryShape.bytes bs.length).size ≤ free.val) (m : ByteView) (i : Nat)
    (outside : i<base ∨ base+32+bs.length ≤ i) (notFree : i<64 ∨ 96 ≤ i) :
    byteAllocationView bs base free fits m i=m i := by
  rw [byteAllocationView,bytesObject_residual bs _ _ base i outside,mstore_outside m 64 i free (by omega)]

theorem byteAllocation_old_region {D} (h : Source.Heap D) (p : Placement h) (bs : List UInt8)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val ≤ base)
    (fits : base+(MemoryShape.bytes bs.length).size ≤ free.val) (m : ByteView)
    (a off : Nat) (present : (h.cells a).isSome) (inside : off<(p.shape a).size) :
    byteAllocationView bs base free fits m (p.address a+off)=m (p.address a+off) := by
  apply byteAllocation_residual
  · have old := p.ends a present; exact Or.inl (by omega)
  · have start := p.starts a present; exact Or.inr (by omega)

/-- The physical allocation encoder decodes to the actual newly allocated
object, and the existing pure writeback leaves the WHOLE allocated heap intact. -/
theorem byteAllocation_writeback {D} (h : Source.Heap D) (p : Placement h) (string : Bool) (bs : List UInt8)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val ≤ base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a ≠ base)
    (fits : base+(MemoryShape.bytes bs.length).size ≤ free.val) (m : ByteView) :
    heapByteWriteback (h.alloc ⟨heapByteType string,heapByteData D string bs⟩).1
      (byteAllocPlacement h p string bs base free after fresh fits) h.next string bs
      (Source.Heap.alloc_get h _) (byteAllocationView bs base free fits m)=
        some (h.alloc ⟨heapByteType string,heapByteData D string bs⟩).1 := by
  have address : (byteAllocPlacement h p string bs base free after fresh fits).address h.next=base := if_pos rfl
  apply heapByteWriteback_unchanged
  · rw [address]
    change (mload (byteAllocationView bs base free fits m) base).val=bs.length
    exact byteAllocation_header bs base free fits m
  · rw [address]
    change readBytes (byteAllocationView bs base free fits m) (base+32) bs.length=bs
    exact byteAllocation_payload bs base free fits m

theorem byteAllocation_state_writeback {E Γ} (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (string : Bool) (bs : List UInt8) (base : Nat) (free : Roadmap.Word) (after : p.free.val ≤ base)
    (fresh : ∀ a, (s.2.heap.cells a).isSome → p.address a ≠ base)
    (fits : base+(MemoryShape.bytes bs.length).size ≤ free.val) (m : ByteView) :
    heapByteStateWriteback (byteAllocatedState s string bs)
      (byteAllocPlacement s.2.heap p string bs base free after fresh fits) s.2.heap.next string bs
      (Source.Heap.alloc_get s.2.heap _) (byteAllocationView bs base free fits m)=
        some (byteAllocatedState s string bs) := by
  unfold heapByteStateWriteback
  change (heapByteWriteback (s.2.heap.alloc ⟨heapByteType string,heapByteData E.layout string bs⟩).1
    (byteAllocPlacement s.2.heap p string bs base free after fresh fits) s.2.heap.next string bs
    (Source.Heap.alloc_get s.2.heap _) (byteAllocationView bs base free fits m)).map
      (withSourceHeap (byteAllocatedState s string bs))=some (byteAllocatedState s string bs)
  rw [byteAllocation_writeback,Option.map_some]
  exact congrArg some (withSourceHeap_unchanged (byteAllocatedState s string bs))

end Solidity.Yul.Views
