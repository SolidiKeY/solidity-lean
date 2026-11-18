import Solidity.Yul.Layout.View
import Solidity.Yul.Views.ObjectMemoryAllocation
import Solidity.Yul.Views.StaticUintMemory

/-!
# The allocation instance facts of the layout view

The two allocation fields of `Shrink.LayoutView.Instances`, for `view`:
`byteAllocation` and `objectAllocation`. Each statement is the field's, with
`view` for `V`.

`alloc` stores the free pointer and then the object (`alloc_at`). A `bytes`
object is `bytesObjectView`, the image of `byteAllocationView`. An object of
words is written first word first, while `wordListView` stores the last word
first; the stores are disjoint, so the two agree (`put_words`, `put_members`).
`objectAllocation` takes the prepared image apart (`alloc_image`): `bytes` and
`string` are the blob case, an array its words (after its length word when it
is dynamic), a struct its member words.
-/
namespace Solidity.Yul.Layout.Instances

open Solidity.Goals
open Solidity.Yul.Views

/-- From a free pointer `base` past the reserved words, an allocation that
ends at the word `free` stores `free` and writes the object at `base`. -/
private theorem alloc_at (P : Shrink.Params) (L : Shrink.Layout) (t : Shrink.Tree)
    (m : Shrink.Phys) (base : Nat) (free : Roadmap.Word) (start : 128 ≤ base)
    (here : m.free = base) (size : free.val = base + allocSize L t) :
    alloc P L t m =
      (allocAt P L base t (m.withMemory (mstore m.memory 64 free))).map fun m' => (base, m') := by
  subst here
  have lt : m.free + allocSize L t < 2 ^ 256 := size ▸ free.isLt
  have word : Shrink.toWord (m.free + allocSize L t) = free :=
    Fin.ext ((Nat.mod_eq_of_lt lt).trans size.symm)
  rw [alloc, if_pos ⟨start, lt⟩, word]

/-- **`byteAllocationView`**: the generic allocation of a blob at the free
pointer is exactly the existing allocation image. -/
theorem byteAllocation (P : Shrink.Params) (bs : List UInt8) (base : Nat) (free : Roadmap.Word)
    (fits : base + (MemoryShape.bytes bs.length).size ≤ free.val) (m : Shrink.Phys) :
    128 ≤ base → m.free = base → free.val = base + (MemoryShape.bytes bs.length).size →
    view.alloc P .bytes (.blob bs) m =
      some (base, m.withMemory (byteAllocationView bs base free fits m.memory)) := by
  intro start here size
  have bound := byteAllocation_length_bound bs base free fits
  change alloc P .bytes (.blob bs) m = _
  rw [alloc_at P .bytes (.blob bs) m base free start here size]
  simp only [allocAt, Shrink.Geometry.write, geometry, dif_pos bound, if_true, Option.map_some]
  rfl

/-! ## Objects of words -/

/-- A word is placed at a memory location by its `mstore`. -/
private theorem put_word (P : Shrink.Params) (a o f : Nat) (w : Roadmap.Word) (m : Shrink.Phys) :
    put P (.scalar 32) ⟨.memory, a, o⟩ (.leaf w.val) f m =
      some (m.withMemory (mstore m.memory a w)) := by
  have lt : w.val < 256 ^ 32 := Nat.lt_of_lt_of_eq w.isLt (by decide)
  have word : Shrink.toWord w.val = w := Fin.ext (Nat.mod_eq_of_lt w.isLt)
  simp only [put, Shrink.Geometry.write, geometry, if_true, Nat.zero_lt_succ, Nat.le_refl,
    true_and, if_pos lt, word]

/-- A store below a serialized list commutes with it. -/
private theorem wordList_mstore (ws : List Roadmap.Word) (b : ByteView) (a base : Nat)
    (w : Roadmap.Word) (below : a + 32 ≤ base) :
    wordListView ws (mstore b a w) base = mstore (wordListView ws b base) a w := by
  induction ws generalizing base with
  | nil => rfl
  | cons v ws ih =>
    rw [wordListView, wordListView, ih (base + 32) (by omega)]
    exact mstore_disjoint_commute _ _ _ _ _ (Or.inl below)

/-- Words placed as array elements from element `i` are their serialized list. -/
private theorem put_words (P : Shrink.Params) (base : Nat) (ws : List Roadmap.Word) (i f : Nat)
    (m : Shrink.Phys) :
    putElems P (.scalar 32) ⟨.memory, base, 0⟩ (ws.map fun w => .leaf w.val) i f m =
      some (m.withMemory (wordListView ws m.memory (base + 32 * i))) := by
  induction ws generalizing i f m with
  | nil => rw [List.map_nil, putElems]; rfl
  | cons w ws ih =>
    have el : geometry.elem P (.scalar 32) ⟨.memory, base, 0⟩ i = ⟨.memory, base + 32 * i, 0⟩ := rfl
    rw [List.map_cons, putElems, el, put_word, Option.bind_some, ih]
    have next : base + 32 * (i + 1) = base + 32 * i + 32 := by omega
    change some (m.withMemory (wordListView ws (mstore m.memory (base + 32 * i) w) _)) = _
    rw [next, wordList_mstore ws _ _ _ w (Nat.le_refl _), wordListView]

/-- The inline offset of a member of a struct of words. -/
private theorem member_offset (n i : Nat) (le : i ≤ n) :
    memberOffset (List.replicate n (.scalar 32)) i = 32 * i := by
  induction n generalizing i with
  | zero => cases i with
    | zero => rfl
    | succ i => omega
  | succ n ih => cases i with
    | zero => rfl
    | succ i =>
      rw [List.replicate_succ, memberOffset, ih i (by omega)]
      change 32 + 32 * i = 32 * (i + 1)
      omega

/-- Words placed as struct members from member `i` are their serialized list. -/
private theorem put_members (P : Shrink.Params) (base n : Nat) (ws : List Roadmap.Word)
    (i f : Nat) (m : Shrink.Phys) (le : i + ws.length ≤ n) :
    putFields P (List.replicate n (.scalar 32)) ⟨.memory, base, 0⟩
        (List.replicate ws.length (.scalar 32)) (ws.map fun w => .leaf w.val) i f m =
      some (m.withMemory (wordListView ws m.memory (base + 32 * i))) := by
  induction ws generalizing i f m with
  | nil => rw [List.map_nil, List.length_nil, List.replicate_zero, putFields]; rfl
  | cons w ws ih =>
    rw [List.length_cons] at le
    have fl : geometry.field P (List.replicate n (.scalar 32)) ⟨.memory, base, 0⟩ i =
        ⟨.memory, base + 32 * i, ((List.replicate n (.scalar 32))[i]?.map indirect).getD 0⟩ := by
      change Shrink.Loc.mk .memory (base + memberOffset _ i) _ = _
      rw [member_offset n i (by omega)]
    rw [List.map_cons, List.length_cons, List.replicate_succ, putFields, fl, put_word,
      Option.bind_some, ih _ _ _ (by omega)]
    have next : base + 32 * (i + 1) = base + 32 * i + 32 := by omega
    change some (m.withMemory (wordListView ws (mstore m.memory (base + 32 * i) w) _)) = _
    rw [next, wordList_mstore ws _ _ _ w (Nat.le_refl _), wordListView]

/-- Words have no out-of-line data, as elements. -/
private theorem tail_words (ws : List Roadmap.Word) :
    tailSizes (.scalar 32) (ws.map fun w => .leaf w.val) = 0 := by
  induction ws with
  | nil => rw [List.map_nil, tailSizes]
  | cons w ws ih => rw [List.map_cons, tailSizes, ih]; rfl

/-- Words have no out-of-line data, as members. -/
private theorem tail_members (ws : List Roadmap.Word) :
    tailFields (List.replicate ws.length (.scalar 32)) (ws.map fun w => .leaf w.val) = 0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons, List.length_cons, List.replicate_succ, tailFields, ih]; rfl

/-- The inline size of a struct of words. -/
private theorem mem_sizes (n : Nat) : memSizes (List.replicate n (.scalar 32)) = n * 32 := by
  induction n with
  | zero => rw [List.replicate_zero, memSizes, Nat.zero_mul]
  | succ n ih => rw [List.replicate_succ, memSizes, ih, memSize]; omega

/-- Words fit a sequence of 32-byte scalars. -/
private theorem fits_words (ws : List Roadmap.Word) :
    Shrink.Layout.FitsAll (.scalar 32) (ws.map fun w => .leaf w.val) := by
  induction ws with
  | nil => rw [List.map_nil, Shrink.Layout.FitsAll]; trivial
  | cons w ws ih =>
    rw [List.map_cons, Shrink.Layout.FitsAll, Shrink.Layout.Fits]
    exact ⟨⟨by decide, by decide, Nat.lt_of_lt_of_eq w.isLt (by decide)⟩, ih⟩

/-- Words fit a struct of 32-byte scalars. -/
private theorem fits_members (ws : List Roadmap.Word) :
    Shrink.Layout.FitsFields (List.replicate ws.length (.scalar 32))
      (ws.map fun w => .leaf w.val) := by
  induction ws with
  | nil => rw [List.map_nil, List.length_nil, List.replicate_zero, Shrink.Layout.FitsFields]; trivial
  | cons w ws ih =>
    rw [List.map_cons, List.length_cons, List.replicate_succ, Shrink.Layout.FitsFields,
      Shrink.Layout.Fits]
    exact ⟨⟨by decide, by decide, Nat.lt_of_lt_of_eq w.isLt (by decide)⟩, ih⟩

/-- A fixed array of words is allocated as its serialized list. -/
private theorem alloc_fixed (P : Shrink.Params) (ws : List Roadmap.Word) (n : Nat)
    (length : ws.length = n) (m : Shrink.Phys)
    (base : Nat) (free : Roadmap.Word) (start : 128 ≤ base) (here : m.free = base)
    (size : free.val = base + n * 32) :
    alloc P (.fixedArray (.scalar 32) n) (.node (ws.map fun w => .leaf w.val)) m =
      some (base, m.withMemory (wordListView ws (mstore m.memory 64 free) base)) := by
  subst length
  have bound : ws.length < 2 ^ 256 := by have lt := free.isLt; omega
  have total : allocSize (.fixedArray (.scalar 32) ws.length)
      (.node (ws.map fun w => .leaf w.val)) = ws.length * 32 := by
    simp only [allocSize, memSize, tailSize, tail_words, Nat.add_zero]
  rw [alloc_at P _ _ m base free start here (total ▸ size)]
  simp only [allocAt, put, List.length_map, true_and, if_pos bound, put_words, Nat.mul_zero,
    Nat.add_zero, Option.map_some]
  rfl

/-- A dynamic array of words is allocated as its length word and its words. -/
private theorem alloc_dynamic (P : Shrink.Params) (ws : List Roadmap.Word) (n : Nat)
    (length : ws.length = n) (bound : n < 2 ^ 256) (m : Shrink.Phys)
    (base : Nat) (free : Roadmap.Word) (start : 128 ≤ base) (here : m.free = base)
    (size : free.val = base + (32 + n * 32)) :
    alloc P (.dynArray (.scalar 32)) (.node (ws.map fun w => .leaf w.val)) m =
      some (base, m.withMemory (wordListView (⟨n, bound⟩ :: ws) (mstore m.memory 64 free) base)) := by
  subst length
  have total : allocSize (.dynArray (.scalar 32)) (.node (ws.map fun w => .leaf w.val)) =
      32 + ws.length * 32 := by
    simp only [allocSize, memSize, tailSize, tail_words, Nat.add_zero, List.length_map]
  have word : Shrink.toWord ws.length = ⟨ws.length, bound⟩ := Fin.ext (Nat.mod_eq_of_lt bound)
  rw [alloc_at P _ _ m base free start here (total ▸ size)]
  simp only [allocAt, List.length_map, if_pos bound, put_words, Nat.mul_zero, Nat.add_zero,
    Option.map_some, word]
  change some (base, (m.withMemory (wordListView ws
    (mstore (mstore m.memory 64 free) base ⟨ws.length, bound⟩) (base + 32)))) = _
  rw [wordList_mstore ws _ _ _ _ (Nat.le_refl _), wordListView]

/-- A struct of words is allocated as its serialized list. -/
private theorem alloc_struct (P : Shrink.Params) (ws : List Roadmap.Word) (n : Nat)
    (length : ws.length = n) (m : Shrink.Phys)
    (base : Nat) (free : Roadmap.Word) (start : 128 ≤ base) (here : m.free = base)
    (size : free.val = base + n * 32) :
    alloc P (.struct (List.replicate n (.scalar 32))) (.node (ws.map fun w => .leaf w.val)) m =
      some (base, m.withMemory (wordListView ws (mstore m.memory 64 free) base)) := by
  subst length
  have total : allocSize (.struct (List.replicate ws.length (.scalar 32)))
      (.node (ws.map fun w => .leaf w.val)) = ws.length * 32 := by
    simp only [allocSize, memSize, tailSize, tail_members, mem_sizes, Nat.add_zero]
  rw [alloc_at P _ _ m base free start here (total ▸ size)]
  simp only [allocAt, put, put_members P base ws.length ws 0 _ _ (Nat.le_of_eq (Nat.zero_add _)),
    Nat.mul_zero, Nat.add_zero, Option.map_some]
  rfl

/-- A prepared image of a shaped object is a generic allocation of the shape's layout. -/
private theorem alloc_image (P : Shrink.Params) {D : Source.Layout} {h : Source.Heap D}
    {q : Placement h} {τ : Source.STy} {data : Source.Data D τ} (prepared : MemoryImage q data)
    (shape : MemoryShape) (shaped : HasMemoryShape data shape) (base : Nat) (free : Roadmap.Word)
    (m : Shrink.Phys) (start : 128 ≤ base) (here : m.free = base)
    (size : free.val = base + shape.size) :
    ∃ t, (Shrink.memoryShapeLayout shape).Fits t ∧
      alloc P (Shrink.memoryShapeLayout shape) t m =
        some (base, m.withMemory (prepared.encode (mstore m.memory 64 free) base)) := by
  cases prepared with
  | bytes bs bound =>
    cases shaped
    change ∃ t, Shrink.Layout.Fits .bytes t ∧ alloc P .bytes t m =
      some (base, m.withMemory (byteAllocationView bs base free (Nat.le_of_eq size.symm) m.memory))
    exact ⟨.blob bs, by rw [Shrink.Layout.Fits]; exact bound,
      byteAllocation P bs base free (Nat.le_of_eq size.symm) m start here size⟩
  | string bs bound =>
    cases shaped
    change ∃ t, Shrink.Layout.Fits .bytes t ∧ alloc P .bytes t m =
      some (base, m.withMemory (byteAllocationView bs base free (Nat.le_of_eq size.symm) m.memory))
    exact ⟨.blob bs, by rw [Shrink.Layout.Fits]; exact bound,
      byteAllocation P bs base free (Nat.le_of_eq size.symm) m start here size⟩
  | words _ ws encoded =>
    cases encoded with
    | value v w _ => cases shaped
    | @array l σ n len hl bound values words elements =>
      cases shaped
      have length : (List.ofFn words).length = len := List.length_ofFn
      have fit := fits_words (List.ofFn words)
      cases n with
      | none =>
        change ∃ t, Shrink.Layout.Fits (.dynArray (.scalar 32)) t ∧
          alloc P (.dynArray (.scalar 32)) t m = some (base, m.withMemory
            (wordListView (⟨len, bound⟩ :: List.ofFn words) (mstore m.memory 64 free) base))
        exact ⟨_, by rw [Shrink.Layout.Fits, List.length_map, length]; exact ⟨bound, fit⟩,
          alloc_dynamic P (List.ofFn words) len length bound m base free start here size⟩
      | some k =>
        change ∃ t, Shrink.Layout.Fits (.fixedArray (.scalar 32) len) t ∧
          alloc P (.fixedArray (.scalar 32) len) t m = some (base, m.withMemory
            (wordListView (List.ofFn words) (mstore m.memory 64 free) base))
        exact ⟨_, by rw [Shrink.Layout.Fits, List.length_map]; exact ⟨length, bound, fit⟩,
          alloc_fixed P (List.ofFn words) len length m base free start here
            (size.trans (congrArg (base + ·) (Nat.zero_add _)))⟩
    | strct fs ws fields =>
      cases shaped
      have fit := fits_members ws
      rw [fields.length] at fit
      change ∃ t, Shrink.Layout.Fits (.struct (List.replicate _ (.scalar 32))) t ∧
        alloc P (.struct (List.replicate _ (.scalar 32))) t m = some (base, m.withMemory
          (wordListView ws (mstore m.memory 64 free) base))
      exact ⟨_, by rw [Shrink.Layout.Fits]; exact fit,
        alloc_struct P ws _ fields.length m base free start here size⟩

/-- **`objectAllocationView`**: every existing object allocation is a generic
allocation of its shape's layout, at the same base and to the same image. -/
theorem objectAllocation (P : Shrink.Params) {D : Source.Layout} (h : Source.Heap D)
    (p : Placement h) {τ : Source.STy} (data : Source.Data D τ) (memory : τ.loc? = some .memory)
    (shape : MemoryShape) (shaped : HasMemoryShape data shape) (base : Nat) (free : Roadmap.Word)
    (after : p.free.val ≤ base) (fresh : ∀ a, (h.cells a).isSome → p.address a ≠ base)
    (fits : base + shape.size ≤ free.val) (m : Shrink.Phys) (image : ByteView) :
    objectAllocationView h p data memory shape shaped base free after fresh fits m.memory =
      some image →
    m.free = base → free.val = base + shape.size →
    ∃ t, (Shrink.memoryShapeLayout shape).Fits t ∧
      view.alloc P (Shrink.memoryShapeLayout shape) t m = some (base, m.withMemory image) := by
  intro view here size
  rw [objectAllocationView, Option.map_eq_some_iff] at view
  obtain ⟨prepared, -, rfl⟩ := view
  exact alloc_image P prepared shape shaped base free m (Nat.le_trans p.free_start after) here size

end Solidity.Yul.Layout.Instances
