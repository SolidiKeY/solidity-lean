import Solidity.Yul.Views.MixedHeapView

namespace Solidity.Yul.Views

/-- Existing encoders consult the residual memory only at the SAME byte.
This is proved from their actual constructors, not an assumed frame law. -/
theorem mstore_residual_point (m m' : ByteView) (base a : Nat) (w : Roadmap.Word)
    (same : m a=m' a) : mstore m base w a=mstore m' base w a := by
  unfold mstore
  split
  · rfl
  · exact same

theorem wordList_residual_point (ws : List Roadmap.Word) (m m' : ByteView) (base a : Nat)
    (same : m a=m' a) : wordListView ws m base a=wordListView ws m' base a := by
  induction ws generalizing base with
  | nil => exact same
  | cons w ws ih => exact mstore_residual_point _ _ base a w (ih (base+32))

theorem MemoryImage.residual_point {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {ty : Source.STy} {d : Source.Data D ty} (image : MemoryImage p d)
    (m m' : ByteView) (base a : Nat) (same : m a=m' a) :
    image.encode m base a=image.encode m' base a := by
  cases image with
  | bytes bs bound =>
    change copyBytes (mstore m base _) _ _ _ _ a=copyBytes (mstore m' base _) _ _ _ _ a
    unfold copyBytes
    split
    · rfl
    · exact mstore_residual_point m m' base a _ same
  | string bs bound =>
    change copyBytes (mstore m base _) _ _ _ _ a=copyBytes (mstore m' base _) _ _ _ _ a
    unfold copyBytes
    split
    · rfl
    · exact mstore_residual_point m m' base a _ same
  | words d ws encoded => exact wordList_residual_point ws m m' base a same

theorem encodeMixedHeap_residual_point {D : Source.Layout} {h : Source.Heap D}
    (p : Placement h) (es : List (MixedHeapEntry p)) (m m' : ByteView) (a : Nat)
    (same : m a=m' a) : encodeMixedHeap p es m a=encodeMixedHeap p es m' a := by
  induction es with
  | nil => exact same
  | cons e es ih => exact e.image.residual_point _ _ (p.address e.id) a ih

/-- Low physical bytes belong to the residual for ordinary allocated objects.
The bound is derived from actual heap lookup and Placement, not a gap guess. -/
theorem encodeMixedHeap_below_reserved {D : Source.Layout} {h : Source.Heap D}
    (p : Placement h) (es : List (MixedHeapEntry p)) (m : ByteView) (a : Nat) (low : a<128) :
    encodeMixedHeap p es m a=m a := by
  apply encodeMixedHeap_residual p es m a
  intro e _
  have present : (h.cells e.id).isSome := by change (h.get e.id).isSome=true; rw [e.found]; rfl
  exact Or.inl (Nat.lt_of_lt_of_le low (p.starts e.id present))

/-- A real scratch interval [destination,destination+size) stays below64.
It therefore commutes with the ENTIRE constructive typed inventory encoding,
including all padding/gaps/residual bytes. No read/output-view law is assumed. -/
theorem encodeMixedHeap_scratch_copy {D : Source.Layout} {h : Source.Heap D}
    (p : Placement h) (es : List (MixedHeapEntry p)) (m src : ByteView)
    (destination start size : Nat) (scratch : destination+size≤64) :
    copyBytes (encodeMixedHeap p es m) src destination start size=
      encodeMixedHeap p es (copyBytes m src destination start size) := by
  funext a
  by_cases inside : destination≤a ∧ a<destination+size
  · have outside : ∀ e ∈ es, a<p.address e.id ∨ p.address e.id+e.image.span≤a := by
      intro e _
      have present : (h.cells e.id).isSome := by change (h.get e.id).isSome=true; rw [e.found]; rfl
      have starts := p.starts e.id present
      exact Or.inl (by omega)
    rw [encodeMixedHeap_residual p es _ a outside]
    simp only [copyBytes,if_pos inside]
  · rw [copyBytes_outside _ _ _ _ _ _ inside]
    exact (encodeMixedHeap_residual_point p es _ _ a (copyBytes_outside _ _ _ _ _ _ inside)).symm

/-- Exact reserved-word/free-pointer preservation, not a weakened MemOK.
The source heap and Placement are unchanged by this physical scratch update. -/
theorem scratch_copy_reserved (m src : ByteView) (free : Roadmap.Word)
    (destination start size : Nat) (scratch : destination+size≤64) (reserved : ReservedOK m free) :
    ReservedOK (copyBytes m src destination start size) free := by
  constructor
  · have same := mload_congr (copyBytes m src destination start size) m 64 (fun i =>
      copyBytes_outside _ _ _ _ _ _ (by have bound:=i.isLt; omega))
    exact (congrArg Fin.val same).trans reserved.1
  · intro i
    rw [copyBytes_outside _ _ _ _ _ _ (by have bound:=i.isLt; omega)]
    exact reserved.2 i

/-- Concrete post-copy images follow from the computed encoder, for every
actual inventory member. Completeness/Nodup are only needed where actually used. -/
theorem scratch_copy_images {D : Source.Layout} {h : Source.Heap D}
    (p : Placement h) (es : List (MixedHeapEntry p)) (distinct : (es.map MixedHeapEntry.id).Nodup)
    (m src : ByteView) (destination start size : Nat) (scratch : destination+size≤64) :
    ∀ e ∈ es, e.image.Reads (copyBytes (encodeMixedHeap p es m) src destination start size) (p.address e.id) := by
  rw [encodeMixedHeap_scratch_copy p es m src destination start size scratch]
  exact encodeMixedHeap_reads p es distinct _

end Solidity.Yul.Views
