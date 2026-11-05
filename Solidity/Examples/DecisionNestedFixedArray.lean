import Solidity.Calculus.DecisionNestedFixedArray
import Solidity.Examples.FixedArrayFloor

/-! # Inhabited two-dimensional fixed-array reconstruction controls
The four distinct original cells distinguish flooring both dimensions from
flooring either dimension alone. No Decision verdict is changed here.
-/
namespace Solidity.Examples.DecisionNestedFixedArray
open Solidity.Decide
set_option Elab.async false

/-- The exact optional-read bridge has inhabited length premises. -/
theorem two_dimensions_bridge (i j : PrimTy.uint.Denote) :
    (nestedFixedFloor [0, 2] [0, 2] FixedArrayFloor.nested).findM
      (.atF i (.atF j .nil)) =
    (SVal.fixed FixedArrayFloor.nested).findM
      (.atF (fixedFloorIndex [0, 2] i) (.atF (fixedFloorIndex [0, 2] j) .nil)) :=
  nestedFixedFloor_find [0, 2] [0, 2] FixedArrayFloor.nested (by decide) (by decide) i j .nil

/-- Both dimensions change: neither single-dimension reconstruction has this value. -/
theorem both_dimensions_change :
    (SVal.fixed FixedArrayFloor.nested).findM
      (.atF (uintOfNat 1) (.atF (uintOfNat 1) .nil)) = some (.prim (uintOfNat 13)) ∧
    (nestedFixedFloor [0, 2] [0, 2] FixedArrayFloor.nested).findM
      (.atF (uintOfNat 1) (.atF (uintOfNat 1) .nil)) = some (.prim (uintOfNat 7)) ∧
    (SVal.fixed (fixedFloorVec [0, 2] FixedArrayFloor.nested)).findM
      (.atF (uintOfNat 1) (.atF (uintOfNat 1) .nil)) = some (.prim (uintOfNat 9)) ∧
    (SVal.fixed (fixedFloorRows [0, 2] FixedArrayFloor.nested)).findM
      (.atF (uintOfNat 1) (.atF (uintOfNat 1) .nil)) = some (.prim (uintOfNat 11)) := by
  decide +kernel

/-- Either out-of-range dimension remains absent when both lengths are retained. -/
theorem both_dimensions_halt :
    (nestedFixedFloor [0, 2] [0, 2] FixedArrayFloor.nested).findM
      (.atF (uintOfNat 2) (.atF (uintOfNat 0) .nil)) = none ∧
    (nestedFixedFloor [0, 2] [0, 2] FixedArrayFloor.nested).findM
      (.atF (uintOfNat 0) (.atF (uintOfNat 2) .nil)) = none := by
  decide +kernel

/-- Omitting the outer length falsifies the proposed floored-read identity. -/
theorem missing_outer_length :
    (nestedFixedFloor [] [0, 2] FixedArrayFloor.nested).findM
      (.atF (uintOfNat 2) (.atF (uintOfNat 0) .nil)) ≠
    (SVal.fixed FixedArrayFloor.nested).findM
      (.atF (fixedFloorIndex [] (uintOfNat 2))
        (.atF (fixedFloorIndex [0, 2] (uintOfNat 0)) .nil)) := by
  decide +kernel

/-- Omitting the inner length independently falsifies that identity. -/
theorem missing_inner_length :
    (nestedFixedFloor [0, 2] [] FixedArrayFloor.nested).findM
      (.atF (uintOfNat 0) (.atF (uintOfNat 2) .nil)) ≠
    (SVal.fixed FixedArrayFloor.nested).findM
      (.atF (fixedFloorIndex [0, 2] (uintOfNat 0))
        (.atF (fixedFloorIndex [] (uintOfNat 2)) .nil)) := by
  decide +kernel

/-- One retained corner reconstructs all four distinct original cells as seven. -/
theorem reconstructed_rectangle : ∀ i j : PrimTy.uint.Denote,
    i.1.toNat < 2 → j.1.toNat < 2 →
    (nestedFixedFloor [0, 2] [0, 2] FixedArrayFloor.nested).findM
      (.atF i (.atF j .nil)) = some (.prim (uintOfNat 7)) := by
  apply nestedFixedFloor_block [0, 2] [0, 2] FixedArrayFloor.nested
    (by decide) (by decide) .nil (fun value => value = some (.prim (uintOfNat 7)))
  intro i j hip hjp hi hj
  have hi0 : i.1.toNat = 0 := by
    rcases hip with h | h
    · exact h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      omega
  have hj0 : j.1.toNat = 0 := by
    rcases hjp with h | h
    · exact h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      omega
  simp only [SVal.findM, FixedArrayFloor.nested, SVec.toList_cons,
    SVec.toList_nil, hi0]
  change (SVal.fixed (.cons (.prim (uintOfNat 7))
    (.cons (.prim (uintOfNat 9)) .nil))).findM (.atF j .nil) = _
  simp only [SVal.findM, SVec.toList_cons, SVec.toList_nil, hj0]
  rfl

end Solidity.Examples.DecisionNestedFixedArray
