import Solidity.Yul.Views.HeapByteMemOK

/-! Actual output placement and two-object read composition. No decoder-length
cap: bounded lengths come from the original valid Placement/physical header.
Physical recomposition preserves arbitrary original residual/padding bytes. -/
namespace Solidity.Yul.Views

def heapByteResultPlacement {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string bs⟩)
    (m : ByteView) (out : Source.Heap D) (e : heapByteWriteback h p a string bs found m = some out) : Placement out :=
  (heapByteWriteback_success h p a string bs found m out e).2.symm ▸
    heapByteWrittenPlacement h p a string bs found m (heapByteWriteback_success h p a string bs found m out e).1

theorem heapByteResult_choices {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string bs⟩)
    (m : ByteView) (out : Source.Heap D) (e : heapByteWriteback h p a string bs found m = some out) :
    (heapByteResultPlacement h p a string bs found m out e).address = p.address ∧
    (heapByteResultPlacement h p a string bs found m out e).shape = p.shape ∧
    (heapByteResultPlacement h p a string bs found m out e).free = p.free := by
  have he := (heapByteWriteback_success h p a string bs found m out e).2
  subst out
  exact ⟨rfl, rfl, rfl⟩

theorem readBytes_congr_on (m m' : ByteView) (a n : Nat)
    (h : ∀ i, i < n → m (a + i) = m' (a + i)) : readBytes m a n = readBytes m' a n := by
  apply List.ext_getElem
  · simp only [readBytes, List.length_map, List.length_range]
  · intro i hi hj
    simp only [readBytes, List.getElem_map, List.getElem_range]
    exact h i (by simpa only [readBytes, List.length_map, List.length_range] using hi)

theorem bytesObject_decode_reencode (m : ByteView) (base : Nat) :
    bytesObjectView (readBytes m (base + 32) (mload m base).val)
      (by simp only [readBytes, List.length_map, List.length_range]; exact (mload m base).isLt) m base = m := by
  apply bytesObject_unchanged
  · apply Fin.ext
    simp only [readBytes, List.length_map, List.length_range]
  · intro i hi
    simp only [readBytes, List.getElem_map, List.getElem_range]

theorem bytesObject_other_object {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a b : Nat) (strA strB : Bool) (oldA oldB bs : List UInt8)
    (ha : h.get a = some ⟨heapByteType strA, heapByteData D strA oldA⟩)
    (hb : h.get b = some ⟨heapByteType strB, heapByteData D strB oldB⟩)
    (distinct : a ≠ b) (hl : bs.length < 2 ^ 256) (sameLength : bs.length = oldA.length)
    (m : ByteView) (header : (mload m (p.address b)).val = oldB.length) :
    mload (bytesObjectView bs hl m (p.address a)) (p.address b) = mload m (p.address b) ∧
    readBytes (bytesObjectView bs hl m (p.address a)) (p.address b + 32) oldB.length =
      readBytes m (p.address b + 32) oldB.length ∧
    decodeHeapByte D strB (bytesObjectView bs hl m (p.address a)) (p.address b) =
      decodeHeapByte D strB m (p.address b) := by
  have present : (h.cells b).isSome := by change (h.get b).isSome = true; rw [hb]; rfl
  have size := byte_shape_live_bound oldB.length
  rw [← heapByte_placement_shape h p b strB oldB hb] at size
  have hm : mload (bytesObjectView bs hl m (p.address a)) (p.address b) = mload m (p.address b) := by
    apply mload_congr
    intro i
    exact bytesObject_other_region h p a b strA oldA bs ha present distinct hl sameLength m i.val (by have hi := i.isLt; omega)
  have hp : readBytes (bytesObjectView bs hl m (p.address a)) (p.address b + 32) oldB.length =
      readBytes m (p.address b + 32) oldB.length := by
    apply readBytes_congr_on
    intro i hi
    simpa only [Nat.add_assoc] using
      bytesObject_other_region h p a b strA oldA bs ha present distinct hl sameLength m (32 + i) (by omega)
  refine ⟨hm, hp, ?_⟩
  rw [decodeHeapByte_data, decodeHeapByte_data, hm, header, hp]

end Solidity.Yul.Views
