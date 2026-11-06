import Solidity.Yul.Views.HeapByteComposition

/-! Separate size-changing ordinary-object preparation. The real input Placement
bounds the new rounded footprint; no arbitrary decoder/fuel cap is introduced.
The fixed-length API/guard is unchanged. None is unsupported preparation, not a
Yul refusal/no-op or all memory-safe semantics. No historical capacity is stored:
a later operation sees its supplied Placement, not an invented allocator history. -/
namespace Solidity.Yul.Views

theorem byteShape_size_mono (n k : Nat) (h : n ≤ k) :
    (MemoryShape.bytes n).size ≤ (MemoryShape.bytes k).size := by
  change 32 + (n + 31) / 32 * 32 ≤ 32 + (k + 31) / 32 * 32
  omega

def heapByteResizeWriteback {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩) (m : ByteView) : Option (Source.Heap D) :=
  if (MemoryShape.bytes (mload m (p.address a)).val).size ≤ (p.shape a).size then
    some (h.write a (decodeHeapByte D string m (p.address a)) (heap_ty_of_get h a _ _ found))
  else none

theorem heapByteResize_success {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (m : ByteView) (out : Source.Heap D) (e : heapByteResizeWriteback h p a string old found m = some out) :
    (MemoryShape.bytes (mload m (p.address a)).val).size ≤ (p.shape a).size ∧
    out = h.write a (decodeHeapByte D string m (p.address a)) (heap_ty_of_get h a _ _ found) := by
  unfold heapByteResizeWriteback at e
  split at e
  · exact ⟨‹_›, (Option.some.inj e).symm⟩
  · cases e

theorem heapByteResize_fixed_compat {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩) (m : ByteView)
    (header : (mload m (p.address a)).val = old.length) :
    heapByteResizeWriteback h p a string old found m = heapByteWriteback h p a string old found m := by
  simp only [heapByteResizeWriteback, heapByteWriteback, header,
    heapByte_placement_shape h p a string old found, Nat.le_refl, if_true]

theorem heapByteResize_unchanged {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩) (m : ByteView)
    (header : (mload m (p.address a)).val = old.length)
    (payload : readBytes m (p.address a + 32) old.length = old) :
    heapByteResizeWriteback h p a string old found m = some h := by
  rw [heapByteResize_fixed_compat h p a string old found m header]
  exact heapByteWriteback_unchanged h p a string old found m header payload

theorem heapByteResize_encode {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (hl : bs.length < 2 ^ 256) (capacity : (MemoryShape.bytes bs.length).size ≤ (p.shape a).size) (m : ByteView) :
    heapByteResizeWriteback h p a string old found (bytesObjectView bs hl m (p.address a)) =
      some (h.write a (heapByteData D string bs) (heap_ty_of_get h a _ _ found)) := by
  simp only [heapByteResizeWriteback, bytesObject_header, if_pos capacity]
  rw [decodeHeapByte_encode]

theorem heapByteResize_other {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a b : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (m : ByteView) (out : Source.Heap D) (e : heapByteResizeWriteback h p a string old found m = some out)
    (other : b ≠ a) : out.get b = h.get b := by
  rw [(heapByteResize_success h p a string old found m out e).2]
  exact Source.Heap.write_other _ other _ _

theorem heapByteResize_types_next {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (m : ByteView) (out : Source.Heap D) (e : heapByteResizeWriteback h p a string old found m = some out) :
    out.ty = h.ty ∧ out.next = h.next ∧ ∀ b, h.next ≤ b → out.cells b = none := by
  rw [(heapByteResize_success h p a string old found m out e).2]
  exact ⟨funext (fun b => Source.Heap.write_ty _ _ b _ _), rfl, fun b hb => (h.write a _ _).bounded b hb⟩

theorem heapByteResize_alias {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a alias : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (m : ByteView) (out : Source.Heap D) (e : heapByteResizeWriteback h p a string old found m = some out)
    (same : alias = a) : out.get alias = some ⟨heapByteType string, decodeHeapByte D string m (p.address a)⟩ := by
  rw [same, (heapByteResize_success h p a string old found m out e).2]
  exact Source.Heap.write_get _ _ _ _

theorem heapByteResize_live_fits {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (m : ByteView) (out : Source.Heap D) (e : heapByteResizeWriteback h p a string old found m = some out) :
    p.address a + 32 + (mload m (p.address a)).val ≤ p.address a + (p.shape a).size ∧
    p.address a + 32 + (mload m (p.address a)).val ≤ p.free.val := by
  have fit := (heapByteResize_success h p a string old found m out e).1
  have live := byte_shape_live_bound (mload m (p.address a)).val
  have present : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  have ends := p.ends a present
  omega

theorem heapByteResize_over_capacity {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩) (m : ByteView)
    (bad : ¬(MemoryShape.bytes (mload m (p.address a)).val).size ≤ (p.shape a).size) :
    heapByteResizeWriteback h p a string old found m = none := by
  simp only [heapByteResizeWriteback, if_neg bad]

theorem heapByteResize_live_view {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (m : ByteView) (out : Source.Heap D) (e : heapByteResizeWriteback h p a string old found m = some out) :
    ∃ bs : List UInt8, ∃ hl : bs.length < 2 ^ 256,
      out.get a = some ⟨heapByteType string, heapByteData D string bs⟩ ∧
      (mload m (p.address a)).val = bs.length ∧
      (∀ i (hi : i < bs.length), bs[i] = m (p.address a + 32 + i)) ∧
      bytesObjectView bs hl m (p.address a) = m := by
  let bs := readBytes m (p.address a + 32) (mload m (p.address a)).val
  have length : bs.length = (mload m (p.address a)).val := by
    simp only [bs, readBytes, List.length_map, List.length_range]
  refine ⟨bs, by rw [length]; exact (mload m (p.address a)).isLt, ?_, length.symm, ?_, ?_⟩
  · rw [heapByteResize_alias h p a a string old found m out e rfl, decodeHeapByte_data]
  · intro i hi
    simp only [bs, readBytes, List.getElem_map, List.getElem_range]
  · exact bytesObject_decode_reencode m (p.address a)

end Solidity.Yul.Views
