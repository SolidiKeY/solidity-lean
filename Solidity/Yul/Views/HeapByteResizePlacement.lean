import Solidity.Yul.Views.HeapByteResize

/-! Actual output Placement: same addresses/free, selected shape changed from
real decoded data, all other shapes unchanged. The input footprint is the bound,
not a guessed global capacity or an allocator-history premise. -/
namespace Solidity.Yul.Views

def heapResizePlacement {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) {τ : Source.STy} (d : Source.Data D τ) (ht : h.ty a = some τ)
    (shape : MemoryShape) (typed : HasMemoryShape d shape) (capacity : shape.size ≤ (p.shape a).size) :
    Placement (h.write a d ht) where
  address := p.address
  shape b := if b = a then shape else p.shape b
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
      simpa only [if_true] using typed
    · simp only [if_neg he]
      exact p.typed b σ x (by rw [Source.Heap.write_other h he] at hb; exact hb)
  starts b hb := p.starts b (by rwa [heap_write_occupancy] at hb)
  ends b hb := by
    have old := p.ends b (by rwa [heap_write_occupancy] at hb)
    by_cases he : b = a
    · subst b
      simp only [if_true]
      exact Nat.le_trans (Nat.add_le_add_left capacity _) old
    · simpa only [if_neg he] using old
  separate b c hb hc hn := by
    have old := p.separate b c (by rwa [heap_write_occupancy] at hb) (by rwa [heap_write_occupancy] at hc) hn
    have smaller (b : Nat) : (if b = a then shape else p.shape b).size ≤ (p.shape b).size := by
      by_cases he : b = a
      · subst b; simpa only [if_true] using capacity
      · simp only [if_neg he, Nat.le_refl]
    rcases old with old | old
    · exact Or.inl (Nat.le_trans (Nat.add_le_add_left (smaller b) _) old)
    · exact Or.inr (Nat.le_trans (Nat.add_le_add_left (smaller c) _) old)

def heapByteResizeWrittenPlacement {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩) (m : ByteView)
    (capacity : (MemoryShape.bytes (mload m (p.address a)).val).size ≤ (p.shape a).size) :
    Placement (h.write a (decodeHeapByte D string m (p.address a)) (heap_ty_of_get h a _ _ found)) :=
  heapResizePlacement h p a _ _ (.bytes (mload m (p.address a)).val)
    (decodeHeapByte_shape D string m (p.address a)) capacity

def heapByteResizeResultPlacement {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (m : ByteView) (out : Source.Heap D) (e : heapByteResizeWriteback h p a string old found m = some out) : Placement out :=
  (heapByteResize_success h p a string old found m out e).2.symm ▸
    heapByteResizeWrittenPlacement h p a string old found m (heapByteResize_success h p a string old found m out e).1

theorem heapByteResize_result_choices {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (m : ByteView) (out : Source.Heap D) (e : heapByteResizeWriteback h p a string old found m = some out) :
    let q := heapByteResizeResultPlacement h p a string old found m out e
    q.address = p.address ∧ q.free = p.free ∧ q.shape a = .bytes (mload m (p.address a)).val ∧
      ∀ b, b ≠ a → q.shape b = p.shape b := by
  have he := (heapByteResize_success h p a string old found m out e).2
  subst out
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp only [heapByteResizeResultPlacement, heapByteResizeWrittenPlacement, heapResizePlacement, if_true]
  · intro b hb
    simp only [heapByteResizeResultPlacement, heapByteResizeWrittenPlacement, heapResizePlacement, if_neg hb]

theorem bytesObject_resize_other_region {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a b : Nat) (string : Bool) (old bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (present : (h.cells b).isSome) (distinct : a ≠ b) (hl : bs.length < 2 ^ 256)
    (capacity : (MemoryShape.bytes bs.length).size ≤ (p.shape a).size)
    (m : ByteView) (off : Nat) (hoff : off < (p.shape b).size) :
    bytesObjectView bs hl m (p.address a) (p.address b + off) = m (p.address b + off) := by
  have ha : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  have sep := p.separate a b ha present distinct
  have live := byte_shape_live_bound bs.length
  apply bytesObject_residual
  omega

theorem bytesObject_shrink_tail (old bs : List UInt8) (ho : old.length < 2 ^ 256)
    (hn : bs.length < 2 ^ 256) (m : ByteView) (base i : Nat)
    (tail : bs.length ≤ i) (live : i < old.length) :
    bytesObjectView bs hn (bytesObjectView old ho m base) base (base + 32 + i) = old[i] := by
  rw [bytesObject_residual bs hn _ base _ (Or.inr (by omega))]
  exact bytesObject_payload old ho m base i live

def heapByteResizeStateWriteback {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (a : Nat) (string : Bool) (old : List UInt8)
    (found : s.2.heap.get a = some ⟨heapByteType string, heapByteData E.layout string old⟩)
    (m : ByteView) : Option (Source.EMState E Γ) :=
  (heapByteResizeWriteback s.2.heap p a string old found m).map (withSourceHeap s)

theorem heapByteResizeState_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy)
    (s out : Source.EMState E Γ) (p : Placement s.2.heap) (a : Nat) (string : Bool) (old : List UInt8)
    (found : s.2.heap.get a = some ⟨heapByteType string, heapByteData E.layout string old⟩)
    (m : ByteView) (e : heapByteResizeStateWriteback s p a string old found m = some out)
    (ok : Source.MemOK E H s) : Source.MemOK E H out := by
  obtain ⟨heap, hw, hs⟩ := Option.map_eq_some_iff.mp e
  subst out
  rw [(heapByteResize_success s.2.heap p a string old found m heap hw).2, decodeHeapByte_data]
  exact heapByte_write_MemOK E H s a string _ _ ok

/-- A relation defined by implemented selected-object writeback, not an assumed
preservation law or a coverage claim about all memory-safe blocks. -/
def heapByteResizeStateStep (E : Source.Env) (Γ : Source.RCtx) (a : Nat) (string : Bool)
    (old : List UInt8) (m : ByteView) (before after : Source.EMState E Γ) : Prop :=
  ∃ p : Placement before.2.heap,
    ∃ found : before.2.heap.get a = some ⟨heapByteType string, heapByteData E.layout string old⟩,
      heapByteResizeStateWriteback before p a string old found m = some after

theorem heapByteResizeState_preserves (E : Source.Env) (Γ : Source.RCtx) (a : Nat)
    (string : Bool) (old : List UInt8) (m : ByteView) :
    PreservesMemOK E (heapByteResizeStateStep E Γ a string old m) := by
  intro H before after ok step
  obtain ⟨p, found, hw⟩ := step
  exact heapByteResizeState_MemOK E H before after p a string old found m hw ok

theorem mstore_object_header_reserved (m : ByteView) (base : Nat) (word free : Roadmap.Word)
    (start : 128 ≤ base) (reserved : ReservedOK m free) : ReservedOK (mstore m base word) free := by
  constructor
  · change readBE (mstore m base word) 64 32 = free.val
    rw [readBE_congr _ m 64 32 (fun i hi => mstore_outside m base (64 + i) word (by omega))]
    exact reserved.1
  · intro i
    rw [mstore_outside m base (96 + i.val) word (by have hi := i.isLt; omega)]
    exact reserved.2 i

end Solidity.Yul.Views
