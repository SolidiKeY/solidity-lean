import Solidity.Yul.Layout.Laws.WriteRead

/-! Checks of `Yul/Layout/Laws/WriteRead.lean`: `write_read` is the same-named
`Shrink.LayoutView.Laws` field of a view over `geometry`, for every allocator,
and is used, given a successful write, on a scalar, on a memory `bytes` object
and on two sibling words. -/
namespace Solidity.Examples.YulLayout.LawsWriteRead

open Solidity.Goals
open Solidity.Yul.Layout

/-- `write_read` is the `Laws.write_read` field. -/
example (V : Shrink.LayoutView) (hV : V.geometry = geometry) :
    ∀ P L l t m m', L.Fits t → V.geometry.write P L l t m = some m' →
      V.geometry.Separated P L l t m' → V.geometry.read P L l m' = some t :=
  hV ▸ write_read

/-- A word reads back wherever its write succeeds; a scalar has no separation premise. -/
example (P : Shrink.Params) (l : Shrink.Loc) (m m' : Shrink.Phys) (v : Nat) (hv : v < 256 ^ 32)
    (h : geometry.write P (.scalar 32) l (.leaf v) m = some m') :
    geometry.read P (.scalar 32) l m' = some (.leaf v) :=
  write_read P _ l _ m m'
    (by simp only [Shrink.Layout.Fits]; exact ⟨by decide, by decide, hv⟩) h
    (by simp only [Shrink.Geometry.Separated])

/-- A memory `bytes` object reads back: its length word ends where its payload starts. -/
example (P : Shrink.Params) (a : Nat) (m m' : Shrink.Phys) (bs : List UInt8)
    (hb : bs.length < 2 ^ 256)
    (h : geometry.write P .bytes ⟨.memory, a, 0⟩ (.blob bs) m = some m') :
    geometry.read P .bytes ⟨.memory, a, 0⟩ m' = some (.blob bs) :=
  write_read P _ _ _ m m' (by simp only [Shrink.Layout.Fits]; exact hb) h (by
    simp only [Shrink.Geometry.Separated, geometry, dataLoc, if_true]
    intro c hc
    cases c with
    | slot r w b => exact hc.1
    | mem x =>
      have head : a ≤ x ∧ x < a + 32 := hc.1
      have payload : a + 32 ≤ x ∧ _ := hc.2
      omega)

/-- Two sibling memory words read back: the second write keeps the first word. -/
example (P : Shrink.Params) (a : Nat) (m m' : Shrink.Phys) (v w : Nat)
    (hv : v < 256 ^ 32) (hw : w < 256 ^ 32)
    (h : geometry.write P (.fixedArray (.scalar 32) 2) ⟨.memory, a, 0⟩
      (.node [.leaf v, .leaf w]) m = some m') :
    geometry.read P (.fixedArray (.scalar 32) 2) ⟨.memory, a, 0⟩ m' =
      some (.node [.leaf v, .leaf w]) :=
  write_read P _ _ _ m m'
    (by
      simp only [Shrink.Layout.Fits, Shrink.Layout.FitsAll, List.length_cons, List.length_nil]
      exact ⟨trivial, by decide, ⟨by decide, by decide, hv⟩, ⟨by decide, by decide, hw⟩,
        trivial⟩)
    h (by
      simp only [Shrink.Geometry.Separated, Shrink.Geometry.ElemsSeparated,
        Shrink.Geometry.cellsT, Shrink.Geometry.elemCellsT, geometry, memSize, if_true, or_false,
        and_true, true_and]
      refine ⟨fun c hc => ?_, fun c hc => hc.2⟩
      cases c with
      | slot r w b => exact hc.1
      | mem x =>
        have first : a + 32 * 0 ≤ x ∧ x < a + 32 * 0 + 32 := hc.1
        have second : a + 32 * (0 + 1) ≤ x ∧ x < a + 32 * (0 + 1) + 32 := hc.2
        omega)

end Solidity.Examples.YulLayout.LawsWriteRead
