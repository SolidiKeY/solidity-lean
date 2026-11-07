import Solidity.Yul.Views.RetainedAllocation
import Solidity.Yul.Views.HeapByteResizeComposition

/-! Constructive finite ordinary byte/string heap realization. Entries are typed
witnesses about actual Heap.get, not another state or untyped intermediate IR.
Every size bound is derived from an actual Placement. Full heap coverage, when
used, is an explicit source support premise; arbitrary objects remain open. -/
namespace Solidity.Yul.Views

structure HeapByteEntry {D : Source.Layout} (h : Source.Heap D) where
  id : Nat
  string : Bool
  bytes : List UInt8
  found : h.get id = some ⟨heapByteType string, heapByteData D string bytes⟩

def encodeByteHeap {D : Source.Layout} {h : Source.Heap D} (p : Placement h) :
    List (HeapByteEntry h) → ByteView → ByteView
  | [], m => m
  | e :: es, m => bytesObjectView e.bytes (heapByte_length_bound h p e.id e.string e.bytes e.found)
      (encodeByteHeap p es m) (p.address e.id)

def HeapByteEntry.Reads {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (e : HeapByteEntry h) (m : ByteView) : Prop :=
  (mload m (p.address e.id)).val = e.bytes.length ∧
    readBytes m (p.address e.id + 32) e.bytes.length = e.bytes

theorem encodeByteHeap_reads {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (HeapByteEntry h)) (distinct : (es.map HeapByteEntry.id).Nodup) (m : ByteView) :
    ∀ e ∈ es, e.Reads p (encodeByteHeap p es m) := by
  induction es with
  | nil => intro e he; cases he
  | cons first rest ih =>
    have nd := List.nodup_cons.mp distinct
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst e
      exact ⟨congrArg Fin.val (bytesObject_header _ _ _ _), bytesObject_payload_list _ _ _ _⟩
    · have prev := ih nd.2 e he
      have different : first.id ≠ e.id := by
        intro eq
        exact nd.1 (List.mem_map.mpr ⟨e, he, eq.symm⟩)
      have keep := bytesObject_resize_other_object h p first.id e.id first.string e.string first.bytes e.bytes first.bytes
        first.found e.found different (heapByte_length_bound h p first.id first.string first.bytes first.found)
        (by rw [heapByte_placement_shape h p first.id first.string first.bytes first.found]; exact Nat.le_refl _)
        (encodeByteHeap p rest m) prev.1
      exact ⟨(congrArg Fin.val keep.1).trans prev.1, keep.2.1.trans prev.2⟩

theorem encodeByteHeap_reserved {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (HeapByteEntry h)) (m : ByteView) (reserved : ReservedOK m p.free) :
    ReservedOK (encodeByteHeap p es m) p.free := by
  induction es with
  | nil => exact reserved
  | cons e es ih =>
    have present : (h.cells e.id).isSome := by change (h.get e.id).isSome = true; rw [e.found]; rfl
    exact bytesObject_reserved _ _ _ _ _ (p.starts e.id present) ih

theorem encodeByteHeap_residual {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (HeapByteEntry h)) (m : ByteView) (i : Nat)
    (outside : ∀ e ∈ es, i < p.address e.id ∨ p.address e.id + 32 + e.bytes.length ≤ i) :
    encodeByteHeap p es m i = m i := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [encodeByteHeap, bytesObject_residual _ _ _ _ _ (outside e (List.mem_cons_self))]
    exact ih (fun x hx => outside x (List.mem_cons_of_mem e hx))

theorem encodeByteHeap_unchanged {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (HeapByteEntry h)) (m : ByteView) (reads : ∀ e ∈ es, e.Reads p m) :
    encodeByteHeap p es m = m := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [encodeByteHeap, ih (fun x hx => reads x (List.mem_cons_of_mem e hx))]
    apply bytesObject_unchanged
    · apply Fin.ext; exact (reads e (List.mem_cons_self)).1
    · intro i hi
      have payload := (reads e (List.mem_cons_self)).2
      have get := congrArg (fun xs => xs[i]?) payload
      have hi' : i < (readBytes m (p.address e.id + 32) e.bytes.length).length := by
        simp only [readBytes, List.length_map, List.length_range]; exact hi
      rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at get
      have value := Option.some.inj get
      simpa only [readBytes, List.getElem_map, List.getElem_range] using value.symm

/-- Exact selected ordinary-byte support, not a replacement for full realization. -/
def CoversByteHeap {D : Source.Layout} {h : Source.Heap D} (es : List (HeapByteEntry h)) : Prop :=
  ∀ a, (h.cells a).isSome → ∃ e ∈ es, e.id = a

theorem encodeByteHeap_realizes {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (HeapByteEntry h)) (distinct : (es.map HeapByteEntry.id).Nodup)
    (coverage : CoversByteHeap es) (m : ByteView) (reserved : ReservedOK m p.free) :
    ReservedOK (encodeByteHeap p es m) p.free ∧
    ∀ a, (h.cells a).isSome → ∃ e ∈ es, e.id = a ∧ e.Reads p (encodeByteHeap p es m) := by
  refine ⟨encodeByteHeap_reserved p es m reserved, ?_⟩
  intro a ha
  obtain ⟨e, he, eq⟩ := coverage a ha
  exact ⟨e, he, eq, encodeByteHeap_reads p es distinct m e he⟩

theorem HeapByteEntry.source_word {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (e : HeapByteEntry h) (m : ByteView) (reads : e.Reads p m) (off : Nat) (w : Roadmap.Word)
    (read : ObjectWord p.address (heapByteData D e.string e.bytes) off w) :
    mload m (p.address e.id + off) = w := by
  rcases e with ⟨id, string, bs, found⟩
  cases string <;> cases read <;> apply Fin.ext <;>
    simpa only [Nat.add_zero] using reads.1

theorem HeapByteEntry.source_byte {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (e : HeapByteEntry h) (m : ByteView) (reads : e.Reads p m) (off : Nat) (v : UInt8)
    (read : ObjectByte (heapByteData D e.string e.bytes) off v) :
    m (p.address e.id + off) = v := by
  have payload (i : Fin e.bytes.length) : m (p.address e.id + 32 + i.val) = e.bytes[i.val] := by
    have get := congrArg (fun xs => xs[i.val]?) reads.2
    have hi : i.val < (readBytes m (p.address e.id + 32) e.bytes.length).length := by
      simp only [readBytes, List.length_map, List.length_range]; exact i.isLt
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem i.isLt] at get
    have value := Option.some.inj get
    simpa only [readBytes, List.getElem_map, List.getElem_range] using value
  rcases e with ⟨id, string, bs, found⟩
  cases string
  · cases read with
    | bytes _ i => simpa only [← Nat.add_assoc] using payload i
  · cases read with
    | string _ i => simpa only [← Nat.add_assoc] using payload i

theorem encodeByteHeap_source_word {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (HeapByteEntry h)) (distinct : (es.map HeapByteEntry.id).Nodup)
    (coverage : CoversByteHeap es) (m : ByteView) (a : Nat) (τ : Source.STy) (d : Source.Data D τ)
    (found : h.get a = some ⟨τ, d⟩) (off : Nat) (w : Roadmap.Word)
    (read : ObjectWord p.address d off w) : mload (encodeByteHeap p es m) (p.address a + off) = w := by
  have present : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  obtain ⟨e, member, same⟩ := coverage a present
  subst a
  have agree := Option.some.inj (found.symm.trans e.found)
  cases agree
  exact e.source_word p _ (encodeByteHeap_reads p es distinct m e member) off w read

theorem encodeByteHeap_source_byte {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (HeapByteEntry h)) (distinct : (es.map HeapByteEntry.id).Nodup)
    (coverage : CoversByteHeap es) (m : ByteView) (a : Nat) (τ : Source.STy) (d : Source.Data D τ)
    (found : h.get a = some ⟨τ, d⟩) (off : Nat) (v : UInt8)
    (read : ObjectByte d off v) : encodeByteHeap p es m (p.address a + off) = v := by
  have present : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  obtain ⟨e, member, same⟩ := coverage a present
  subst a
  have agree := Option.some.inj (found.symm.trans e.found)
  cases agree
  exact e.source_byte p _ (encodeByteHeap_reads p es distinct m e member) off v read

end Solidity.Yul.Views
