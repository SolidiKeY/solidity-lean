import Solidity.Yul.Views.HeapByteResizePlacement

/-! Nonoverlapping object decode preservation for actual bounded size changes.
The other object's correct-header premise remains necessary; arbitrary raw writes
are not presumed safe. -/
namespace Solidity.Yul.Views

theorem bytesObject_resize_other_object {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a b : Nat) (strA strB : Bool) (oldA oldB bs : List UInt8)
    (ha : h.get a = some ⟨heapByteType strA, heapByteData D strA oldA⟩)
    (hb : h.get b = some ⟨heapByteType strB, heapByteData D strB oldB⟩)
    (distinct : a ≠ b) (hl : bs.length < 2 ^ 256)
    (capacity : (MemoryShape.bytes bs.length).size ≤ (p.shape a).size)
    (m : ByteView) (header : (mload m (p.address b)).val = oldB.length) :
    mload (bytesObjectView bs hl m (p.address a)) (p.address b) = mload m (p.address b) ∧
    readBytes (bytesObjectView bs hl m (p.address a)) (p.address b + 32) oldB.length =
      readBytes m (p.address b + 32) oldB.length ∧
    decodeHeapByte D strB (bytesObjectView bs hl m (p.address a)) (p.address b) = decodeHeapByte D strB m (p.address b) := by
  have present : (h.cells b).isSome := by change (h.get b).isSome = true; rw [hb]; rfl
  have size := byte_shape_live_bound oldB.length
  rw [← heapByte_placement_shape h p b strB oldB hb] at size
  have hm : mload (bytesObjectView bs hl m (p.address a)) (p.address b) = mload m (p.address b) := by
    apply mload_congr
    intro i
    exact bytesObject_resize_other_region h p a b strA oldA bs ha present distinct hl capacity m i.val (by have hi := i.isLt; omega)
  have hp : readBytes (bytesObjectView bs hl m (p.address a)) (p.address b + 32) oldB.length = readBytes m (p.address b + 32) oldB.length := by
    apply readBytes_congr_on
    intro i hi
    simpa only [Nat.add_assoc] using bytesObject_resize_other_region h p a b strA oldA bs ha present distinct hl capacity m (32 + i) (by omega)
  refine ⟨hm, hp, ?_⟩
  rw [decodeHeapByte_data, decodeHeapByte_data, hm, header, hp]

end Solidity.Yul.Views
