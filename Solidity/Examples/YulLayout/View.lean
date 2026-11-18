import Solidity.Yul.Layout.Laws

/-! Checks of the layout view: its allocator on small concrete trees, and
each allocation law, `view_geometric` and `view_laws` used once. -/
namespace Solidity.Examples.YulLayout.View

open Solidity.Goals
open Solidity.Yul.Views
open Solidity.Yul.Layout

/-- A `uint[]` inside a struct is a two-word header; its two words are out of line. -/
example : memSize (.struct [.scalar 32, .dynArray (.scalar 32)]) = 96 ∧
    tailSize (.struct [.scalar 32, .dynArray (.scalar 32)])
      (.node [.leaf 7, .node [.leaf 1, .leaf 2]]) = 64 ∧
    allocSize (.struct [.scalar 32, .dynArray (.scalar 32)])
      (.node [.leaf 7, .node [.leaf 1, .leaf 2]]) = 160 :=
  ⟨rfl, rfl, rfl⟩

/-- A root `bytes` of three bytes takes its length word and one payload word. -/
example : allocSize .bytes (.blob [1, 2, 3]) = 64 := rfl

/-- A word placed at a memory address is the `mstore` there. -/
example (P : Shrink.Params) (m : Shrink.Phys) :
    put P (.scalar 32) ⟨.memory, 128, 0⟩ (.leaf 5) 160 m =
      some (m.withMemory (mstore m.memory 128 (Shrink.toWord 5))) := by
  simp only [put, Shrink.Geometry.write, geometry, ↓reduceIte, Nat.zero_lt_succ, Nat.le_refl,
    true_and, if_pos (by decide : 5 < 256 ^ 32)]

/-- No elements and no members are placed without a write. -/
example (P : Shrink.Params) (l : Shrink.Loc) (m : Shrink.Phys) :
    putElems P .bytes l [] 0 0 m = some m ∧ putFields P [] l [] [] 0 0 m = some m :=
  ⟨by rw [putElems], by rw [putFields]⟩

/-- An empty root dynamic array at `a` is its zero length word. -/
example (P : Shrink.Params) (m : Shrink.Phys) (a : Nat) :
    allocAt P (.dynArray .bytes) a (.node []) m =
      some (m.withMemory (mstore m.memory a (Shrink.toWord 0))) := by
  simp only [allocAt, List.length_nil, if_pos (by decide : 0 < 2 ^ 256), putElems]

/-- The allocator refuses a free pointer inside the reserved words. -/
example (P : Shrink.Params) (L : Shrink.Layout) (t : Shrink.Tree) (m : Shrink.Phys)
    (h : m.free < 128) : alloc P L t m = none := by
  rw [alloc, if_neg (by omega)]

/-- The view is the geometry with the allocator. -/
example : view.geometry = geometry ∧ view.alloc = alloc := ⟨rfl, rfl⟩

/-- The view packs `bytes8` elements four to a slot (`Geometric.elem`). -/
example (P : Shrink.Params) :
    view.geometry.elem P (.scalar 8) ⟨.storage, 0, 0⟩ 5 = ⟨.storage, 1, 8⟩ :=
  (view_geometric.elem P .storage 8 0 5 (by decide) (by decide)).trans rfl

/-- `alloc_read` is the `Laws.alloc_read` field at `view`. -/
example : ∀ P L t m a m', L.Fits t → view.alloc P L t m = some (a, m') →
    view.geometry.read P L ⟨.memory, a, 0⟩ m' = some t ∧ m.free ≤ a ∧
    (∀ c, view.geometry.cells P L ⟨.memory, a, 0⟩ m' c →
      ∃ x, c = .mem x ∧ m.free ≤ x ∧ x < m'.free) ∧
    m'.storage = m.storage ∧ m'.transient = m.transient ∧
    (∀ x, x < m.free → (x < 64 ∨ 96 ≤ x) → m'.memory x = m.memory x) :=
  alloc_read

/-- `alloc_total` is the `Laws.alloc_total` field at `view`. -/
example : ∀ P L t m, L.NoMapping → L.Fits t → 128 ≤ m.free →
    m.free + 64 * t.weight < 2 ^ 256 → ∃ a m', view.alloc P L t m = some (a, m') :=
  alloc_total

/-- A `bytes[1]` of any byte string is allocated when it fits the address
space: the nested `bytes` is an indirect header the allocator builds. -/
example (P : Shrink.Params) (m : Shrink.Phys) (bs : List UInt8) (start : 128 ≤ m.free)
    (room : m.free + 64 * (3 + bs.length) < 2 ^ 256) :
    ∃ a m', view.alloc P (.fixedArray .bytes 1) (.node [.blob bs]) m = some (a, m') :=
  alloc_total P _ _ m (by simp only [Shrink.Layout.NoMapping])
    (by
      simp only [Shrink.Layout.Fits, Shrink.Layout.FitsAll]
      exact ⟨rfl, by decide, by omega, trivial⟩)
    start (by
      simp only [Shrink.Tree.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega)

/-- An allocated `uint[][]` is read back at the old free pointer, and the
allocation keeps storage. -/
example (P : Shrink.Params) (m m' : Shrink.Phys) (a : Nat)
    (h : view.alloc P (.dynArray (.dynArray (.scalar 32)))
      (.node [.node [.leaf 1, .leaf 2], .node []]) m = some (a, m')) :
    view.geometry.read P (.dynArray (.dynArray (.scalar 32))) ⟨.memory, a, 0⟩ m' =
        some (.node [.node [.leaf 1, .leaf 2], .node []]) ∧
      a = m.free ∧ m'.storage = m.storage := by
  have law := view_laws.alloc_read P _ _ m a m' (by
    simp only [Shrink.Layout.Fits, Shrink.Layout.FitsAll, List.length_cons, List.length_nil]
    decide) h
  have at_free : alloc P (.dynArray (.dynArray (.scalar 32)))
      (.node [.node [.leaf 1, .leaf 2], .node []]) m = some (a, m') := h
  rw [alloc] at at_free
  split at at_free
  · cases hw : allocAt P (.dynArray (.dynArray (.scalar 32))) m.free
        (.node [.node [.leaf 1, .leaf 2], .node []])
        (m.withMemory (mstore m.memory 64 (Shrink.toWord (m.free +
          allocSize (.dynArray (.dynArray (.scalar 32)))
            (.node [.node [.leaf 1, .leaf 2], .node []]))))) with
    | none => rw [hw] at at_free; cases at_free
    | some m₁ =>
      rw [hw] at at_free
      cases at_free
      exact ⟨law.1, rfl, law.2.2.2.1⟩
  · cases at_free

/-- A `bytes` allocation at the free pointer is the image `byteAllocationView`
(the statement of `LayoutView.Instances.byteAllocation` at `view`). -/
example (P : Shrink.Params) (bs : List UInt8) (base : Nat) (free : Roadmap.Word)
    (fits : base + (MemoryShape.bytes bs.length).size ≤ free.val) (m : Shrink.Phys)
    (start : 128 ≤ base) (at_free : m.free = base)
    (next : free.val = base + (MemoryShape.bytes bs.length).size) :
    view.alloc P .bytes (.blob bs) m =
      some (base, m.withMemory (byteAllocationView bs base free fits m.memory)) := by
  have size : allocSize .bytes (.blob bs) = (MemoryShape.bytes bs.length).size := rfl
  have word : Shrink.toWord (base + (MemoryShape.bytes bs.length).size) = free :=
    Fin.ext ((Nat.mod_eq_of_lt (next ▸ free.isLt)).trans next.symm)
  have len := byteAllocation_length_bound bs base free fits
  change alloc P .bytes (.blob bs) m = _
  rw [alloc, at_free, size, if_pos ⟨start, next ▸ free.isLt⟩, word]
  simp only [allocAt, Shrink.Geometry.write, geometry, ↓reduceIte, dif_pos len, Option.map_some]
  rfl

end Solidity.Examples.YulLayout.View
