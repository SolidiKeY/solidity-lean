import Solidity.Yul.Layout.Laws.Write

/-! Checks of the write laws of the layout geometry: each law is the
same-named `Shrink.LayoutView.Laws` field of a view over `geometry`, for every
allocator, and is used once on a concrete write. -/
namespace Solidity.Examples.YulLayout.LawsWrite

open Solidity.Goals
open Solidity.Yul.Layout

/-- `illTyped` is the `Laws.illTyped` field. -/
example (V : Shrink.LayoutView) (hV : V.geometry = geometry) :
    ∀ P L l t m, ¬ L.Fits t → V.geometry.write P L l t m = none :=
  hV ▸ illTyped

/-- `write_total` is the `Laws.write_total` field. -/
example (V : Shrink.LayoutView) (hV : V.geometry = geometry) :
    ∀ P L l t m, l.region ≠ .memory → L.NoMapping → L.Fits t →
      ∃ m', V.geometry.write P L l t m = some m' :=
  hV ▸ write_total

/-- `frame` is the `Laws.frame` field. -/
example (V : Shrink.LayoutView) (hV : V.geometry = geometry) :
    ∀ P L l t m m', V.geometry.write P L l t m = some m' →
      ∀ c, ¬ V.geometry.cellsT P L l t m' c → m'.byte c = m.byte c :=
  hV ▸ frame

/-- A one-byte scalar does not hold 256, at any location. -/
example (P : Shrink.Params) (l : Shrink.Loc) (m : Shrink.Phys) :
    geometry.write P (.scalar 1) l (.leaf 256) m = none :=
  illTyped P _ l _ m (by simp only [Shrink.Layout.Fits]; decide)

/-- A storage `bytes[1]` takes any byte string. -/
example (P : Shrink.Params) (m : Shrink.Phys) (bs : List UInt8) (h : bs.length < 2 ^ 256) :
    ∃ m', geometry.write P (.fixedArray .bytes 1) ⟨.storage, 0, 0⟩ (.node [.blob bs]) m = some m' :=
  write_total P _ _ _ m (by decide) (by simp only [Shrink.Layout.NoMapping])
    (by simp only [Shrink.Layout.Fits, Shrink.Layout.FitsAll]; exact ⟨rfl, by decide, h, trivial⟩)

/-- A storage word write keeps transient storage and memory. -/
example (P : Shrink.Params) (m m' : Shrink.Phys) (v : Nat)
    (h : geometry.write P (.scalar 32) ⟨.storage, 0, 0⟩ (.leaf v) m = some m')
    (w : Roadmap.Word) (b a : Nat) :
    m'.byte (.slot .transient w b) = m.byte (.slot .transient w b) ∧
      m'.byte (.mem a) = m.byte (.mem a) :=
  ⟨frame P _ _ _ m m' h _ (by
      simp only [Shrink.Geometry.cellsT, geometry, slotField, Nat.reducePow, exists_and_left,
        reduceCtorEq, ↓reduceIte, Nat.zero_lt_succ, Nat.zero_add, Nat.le_refl, and_self,
        ↓reduceDIte, Shrink.Cell.slot.injEq, false_and, Nat.zero_le, true_and, exists_const,
        not_false_eq_true]),
    frame P _ _ _ m m' h _ (by
      simp only [Shrink.Geometry.cellsT, geometry, slotField, Nat.reducePow, exists_and_left,
        reduceCtorEq, ↓reduceIte, Nat.zero_lt_succ, Nat.zero_add, Nat.le_refl, and_self,
        ↓reduceDIte, Nat.zero_le, true_and, false_and, exists_const, not_false_eq_true])⟩

end Solidity.Examples.YulLayout.LawsWrite
