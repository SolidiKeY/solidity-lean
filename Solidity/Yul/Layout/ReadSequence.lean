import Solidity.Goals.Shrink

/-! Element-sequence locality for the existing recursive layout reader.
This shared induction step is part of the measured `yulLayoutPilot` experiment.
-/
namespace Solidity.Yul.Layout

open Solidity.Goals

/-- Pointwise equality of the element reads gives equality of the sequence read.
The interval premise permits the same lemma to serve a recursive suffix. -/
theorem readElems_congr (G : Shrink.Geometry) (P : Shrink.Params) (e : Shrink.Layout) (l : Shrink.Loc)
    (n i : Nat) (m m' : Shrink.Phys)
    (h : ∀ j, i ≤ j → j < i + n →
      G.read P e (G.elem P e l j) m = G.read P e (G.elem P e l j) m') :
    G.readElems P e l n i m = G.readElems P e l n i m' := by
  induction n generalizing i with
  | zero => simp only [Shrink.Geometry.readElems]
  | succ n ih =>
    simp only [Shrink.Geometry.readElems]
    rw [h i (Nat.le_refl i) (by omega)]
    rw [ih (i + 1) (by
      intro j hj hjn
      exact h j (by omega) (by omega))]

end Solidity.Yul.Layout
