import Solidity.Yul.Views.HeapByteWriteback

/-! Preserve the ORIGINAL placement choices: address/shape/free are not changed.
Size/header facts come from actual allocated objects. Physical encoders preserve
reserved words, padding and every nonoverlapping object's live region. -/
namespace Solidity.Yul.Views

theorem heap_write_occupancy {D : Source.Layout} (h : Source.Heap D) (a b : Nat)
    {τ : Source.STy} (d : Source.Data D τ) (ht : h.ty a = some τ) :
    ((h.write a d ht).cells b).isSome = (h.cells b).isSome := by
  have he := congrArg Option.isSome (Source.Heap.write_ty h a b d ht)
  simpa only [Source.Heap.ty, Option.isSome_map] using he

/-- Transport only, preserving the same physical choices and all old bounds. -/
def heapWritePlacement {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) {τ : Source.STy} (d : Source.Data D τ) (ht : h.ty a = some τ)
    (shape : HasMemoryShape d (p.shape a)) : Placement (h.write a d ht) where
  address := p.address
  shape := p.shape
  free := p.free
  free_start := p.free_start
  distinct b c hb hc he := p.distinct b c
    (by rwa [heap_write_occupancy] at hb) (by rwa [heap_write_occupancy] at hc) he
  typed b σ x hb := by
    change (h.write a d ht).get b = some ⟨σ, x⟩ at hb
    by_cases he : b = a
    · subst b
      rw [Source.Heap.write_get] at hb
      cases hb
      exact shape
    · exact p.typed b σ x (by rw [Source.Heap.write_other h he] at hb; exact hb)
  starts b hb := p.starts b (by rwa [heap_write_occupancy] at hb)
  ends b hb := p.ends b (by rwa [heap_write_occupancy] at hb)
  separate b c hb hc hn := p.separate b c
    (by rwa [heap_write_occupancy] at hb) (by rwa [heap_write_occupancy] at hc) hn

theorem decodeHeapByte_shape (D : Source.Layout) (string : Bool) (m : ByteView) (base : Nat) :
    HasMemoryShape (decodeHeapByte D string m base) (.bytes (mload m base).val) := by
  rw [decodeHeapByte_data]
  have hl : (readBytes m (base + 32) (mload m base).val).length = (mload m base).val := by
    simp only [readBytes, List.length_map, List.length_range]
  have hs := heapByteData_shape D string (readBytes m (base + 32) (mload m base).val)
  rw [hl] at hs
  exact hs

def heapByteWrittenPlacement {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string bs⟩) (m : ByteView)
    (header : (mload m (p.address a)).val = bs.length) :
    Placement (h.write a (decodeHeapByte D string m (p.address a)) (heap_ty_of_get h a _ _ found)) :=
  heapWritePlacement h p a _ _ (by
    rw [heapByte_placement_shape h p a string bs found, ← header]
    exact decodeHeapByte_shape D string m (p.address a))

theorem heapByte_placement_choices {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string bs⟩) (m : ByteView)
    (header : (mload m (p.address a)).val = bs.length) :
    (heapByteWrittenPlacement h p a string bs found m header).address = p.address ∧
    (heapByteWrittenPlacement h p a string bs found m header).shape = p.shape ∧
    (heapByteWrittenPlacement h p a string bs found m header).free = p.free := ⟨rfl, rfl, rfl⟩

theorem bytesObject_reserved (bs : List UInt8) (hl : bs.length < 2 ^ 256)
    (m : ByteView) (base : Nat) (free : Roadmap.Word) (start : 128 ≤ base)
    (reserved : ReservedOK m free) : ReservedOK (bytesObjectView bs hl m base) free := by
  constructor
  · change readBE (bytesObjectView bs hl m base) 64 32 = free.val
    rw [readBE_congr _ m 64 32 (fun i hi => bytesObject_residual bs hl m base (64 + i) (Or.inl (by omega)))]
    exact reserved.1
  · intro i
    rw [bytesObject_residual bs hl m base (96 + i.val) (Or.inl (by have hi := i.isLt; omega))]
    exact reserved.2 i

theorem bytesObject_other_region {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a b : Nat) (string : Bool) (old bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (present : (h.cells b).isSome) (distinct : a ≠ b) (hl : bs.length < 2 ^ 256)
    (sameLength : bs.length = old.length) (m : ByteView) (off : Nat) (hoff : off < (p.shape b).size) :
    bytesObjectView bs hl m (p.address a) (p.address b + off) = m (p.address b + off) := by
  have ha : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  have sep := p.separate a b ha present distinct
  have live := byte_shape_live_bound old.length
  rw [← heapByte_placement_shape h p a string old found] at live
  apply bytesObject_residual
  rw [sameLength]
  omega

theorem heap_writes_commute {D : Source.Layout} (h : Source.Heap D) (a b : Nat)
    {τ σ : Source.STy} (x : Source.Data D τ) (y : Source.Data D σ)
    (ha : h.ty a = some τ) (hb : h.ty b = some σ) (distinct : a ≠ b) :
    (h.write a x ha).write b y (by rw [Source.Heap.write_ty]; exact hb) =
    (h.write b y hb).write a x (by rw [Source.Heap.write_ty]; exact ha) := by
  apply heap_cells_ext
    ((h.write a x ha).write b y (by rw [Source.Heap.write_ty]; exact hb))
    ((h.write b y hb).write a x (by rw [Source.Heap.write_ty]; exact ha)) ?_ rfl
  funext c
  by_cases hca : c = a
  · subst c
    simp only [Source.Heap.write, if_neg distinct, if_true]
  · by_cases hcb : c = b
    · subst c
      simp only [Source.Heap.write, if_neg (Ne.symm distinct), if_true]
    · simp only [Source.Heap.write, if_neg hca, if_neg hcb]

end Solidity.Yul.Views
