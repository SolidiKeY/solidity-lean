import Solidity.Yul.Views.MemoryImages

/-! Constructive mixed ordinary heap view. Entries retain actual typed source
contents and constructor-derived images. This is not a replacement heap/IR. -/
namespace Solidity.Yul.Views

structure MixedHeapEntry {D : Source.Layout} {h : Source.Heap D} (p : Placement h) where
  id : Nat
  ty : Source.STy
  data : Source.Data D ty
  found : h.get id = some ⟨ty, data⟩
  image : MemoryImage p data

def encodeMixedHeap {D : Source.Layout} {h : Source.Heap D} (p : Placement h) :
    List (MixedHeapEntry p) → ByteView → ByteView
  | [], m => m
  | e :: es, m => e.image.encode (encodeMixedHeap p es m) (p.address e.id)

theorem mixed_other_region {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (e f : MixedHeapEntry p) (distinct : e.id ≠ f.id) (m : ByteView) (i : Nat) (hi : i < f.image.span) :
    e.image.encode m (p.address e.id) (p.address f.id + i) = m (p.address f.id + i) := by
  have present (e : MixedHeapEntry p) : (h.cells e.id).isSome := by change (h.get e.id).isSome = true; rw [e.found]; rfl
  have sep := p.separate e.id f.id (present e) (present f) distinct
  have eb := e.image.fits p e.id e.found
  have fb := f.image.fits p f.id f.found
  exact e.image.residual m _ _ (by omega)

theorem encodeMixedHeap_reads {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (distinct : (es.map MixedHeapEntry.id).Nodup) (m : ByteView) :
    ∀ e ∈ es, e.image.Reads (encodeMixedHeap p es m) (p.address e.id) := by
  induction es with
  | nil => intro e he; cases he
  | cons e es ih =>
    have nd := List.nodup_cons.mp distinct
    intro f hf
    rcases List.mem_cons.mp hf with hf | hf
    · subst f; exact e.image.encode_reads _ _
    · apply f.image.reads_congr _ (encodeMixedHeap p es m) _
      · intro i hi
        apply mixed_other_region p e f _ _ i hi
        intro eq
        exact nd.1 (List.mem_map.mpr ⟨f, hf, eq.symm⟩)
      · exact ih nd.2 f hf

theorem encodeMixedHeap_reserved {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (m : ByteView) (reserved : ReservedOK m p.free) :
    ReservedOK (encodeMixedHeap p es m) p.free := by
  induction es with
  | nil => exact reserved
  | cons e es ih =>
    have present : (h.cells e.id).isSome := by change (h.get e.id).isSome = true; rw [e.found]; rfl
    exact e.image.reserved _ _ p.free (p.starts e.id present) ih

theorem encodeMixedHeap_residual {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (m : ByteView) (a : Nat)
    (outside : ∀ e ∈ es, a < p.address e.id ∨ p.address e.id + e.image.span ≤ a) :
    encodeMixedHeap p es m a = m a := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [encodeMixedHeap, e.image.residual _ _ _ (outside e List.mem_cons_self)]
    exact ih (fun f hf => outside f (List.mem_cons_of_mem e hf))

theorem encodeMixedHeap_unchanged {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (m : ByteView)
    (reads : ∀ e ∈ es, e.image.Reads m (p.address e.id)) : encodeMixedHeap p es m = m := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [encodeMixedHeap, ih (fun f hf => reads f (List.mem_cons_of_mem e hf))]
    exact e.image.unchanged m _ (reads e List.mem_cons_self)

def CoversMixedHeap {D : Source.Layout} {h : Source.Heap D} {p : Placement h} (es : List (MixedHeapEntry p)) : Prop :=
  ∀ a, (h.cells a).isSome → ∃ e ∈ es, e.id = a

theorem encodeMixedHeap_source_word {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (distinct : (es.map MixedHeapEntry.id).Nodup) (coverage : CoversMixedHeap es)
    (m : ByteView) (a : Nat) (τ : Source.STy) (d : Source.Data D τ) (found : h.get a = some ⟨τ, d⟩)
    (off : Nat) (w : Roadmap.Word) (read : ObjectWord p.address d off w) :
    mload (encodeMixedHeap p es m) (p.address a + off) = w := by
  have present : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  obtain ⟨e, member, eq⟩ := coverage a present
  subst a
  have same := Option.some.inj (found.symm.trans e.found)
  cases same
  exact e.image.source_word _ _ off (encodeMixedHeap_reads p es distinct m e member) w read

theorem encodeMixedHeap_source_byte {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (distinct : (es.map MixedHeapEntry.id).Nodup) (coverage : CoversMixedHeap es)
    (m : ByteView) (a : Nat) (τ : Source.STy) (d : Source.Data D τ) (found : h.get a = some ⟨τ, d⟩)
    (off : Nat) (v : UInt8) (read : ObjectByte d off v) :
    encodeMixedHeap p es m (p.address a + off) = v := by
  have present : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  obtain ⟨e, member, eq⟩ := coverage a present
  subst a
  have same := Option.some.inj (found.symm.trans e.found)
  cases same
  exact e.image.source_byte _ _ off (encodeMixedHeap_reads p es distinct m e member) v read

end Solidity.Yul.Views
