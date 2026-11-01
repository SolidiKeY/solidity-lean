import Solidity.Calculus.DecisionFixedArrayPair
import Solidity.Examples.DecisionFixedArrayPath

/-! # Two-array reconstruction and overlap controls
Value/path kernel controls only; no array decision coverage is promoted.
-/
namespace Solidity.Examples.DecisionFixedArrayPair
open Solidity.Decide
open Solidity.Examples.DecisionFixedArrayPath (inner mapping nested)
set_option Elab.async false

abbrev MapTy : Ty := .ref (.mapping .uint (.ref (.fixed (.prim .uint) 3)))

def leftPath : Path MapTy (.ref (.fixed (.prim .uint) 3)) := .key (uintOfNat 5) .nil
def rightPath : Path MapTy (.ref (.fixed (.prim .uint) 3)) := .key (uintOfNat 6) .nil

theorem paths_diverge : Path.Diverges leftPath rightPath := .key .nil .nil (by decide +kernel)

theorem left_present : mapping.findM leftPath = some inner := by decide +kernel

theorem right_present : mapping.findM rightPath = some inner := by decide +kernel

/-- The generic simultaneous API is inhabited by actual typed values and saves. -/
theorem actual_pair_exists : ∃ z, fixedFloorPair leftPath [1, 3] rightPath [2, 3] mapping = some z :=
  fixedFloorPair_exists leftPath [1, 3] rightPath [2, 3] mapping paths_diverge left_present right_present

/-- Both equations follow from the generic proof, not a computed verdict assumption. -/
theorem actual_pair_client : ∃ z,
    fixedFloorPair leftPath [1, 3] rightPath [2, 3] mapping = some z ∧
    z.findM (leftPath.append (.atF (uintOfNat 2) .nil)) =
      mapping.findM (leftPath.append (.atF (fixedFloorIndex [1, 3] (uintOfNat 2)) .nil)) ∧
    z.findM (rightPath.append (.atF (uintOfNat 1) .nil)) =
      mapping.findM (rightPath.append (.atF (fixedFloorIndex [2, 3] (uintOfNat 1)) .nil)) := by
  obtain ⟨z, hz⟩ := actual_pair_exists
  exact ⟨z, hz, fixedFloorPair_find_left _ _ _ _ _ hz paths_diverge (by decide) _ _,
    fixedFloorPair_find_right _ _ _ _ _ hz paths_diverge (by decide) _ _⟩

/-- Both selected values change while a third key retains its original observation. -/
theorem both_changed_and_frame : ∃ z,
    fixedFloorPair leftPath [1, 3] rightPath [2, 3] mapping = some z ∧
    z.findM (.key (uintOfNat 5) (.atF (uintOfNat 2) .nil)) = some (.prim (uintOfNat 9)) ∧
    z.findM (.key (uintOfNat 6) (.atF (uintOfNat 1) .nil)) = some (.prim (uintOfNat 7)) ∧
    z.findM (.key (uintOfNat 7) (.atF (uintOfNat 1) .nil)) = some (.prim (uintOfNat 9)) := by
  decide +kernel

/-- A genuinely absent sibling array remains a refusal after a successful first rebuild. -/
theorem absent_second_refused : fixedFloorPair (.atF (uintOfNat 1) .nil) [1, 3]
    (.atF (uintOfNat 2) .nil) [2, 3] nested = none := by
  decide +kernel

/-- Length retention alone cannot replace the explicit divergence premise. -/
theorem overlap_breaks_first_equation : ∃ z : SVal (.ref (.fixed (.prim .uint) 3)),
    fixedFloorPair .nil [1, 3] .nil [2, 3] inner = some z ∧
    z.findM (.atF (uintOfNat 1) .nil) ≠
      inner.findM (.atF (fixedFloorIndex [1, 3] (uintOfNat 1)) .nil) := by
  decide +kernel

theorem overlap_not_divergent : ¬ Path.Diverges
    (Path.nil : Path (.ref (.fixed (.prim .uint) 3)) (.ref (.fixed (.prim .uint) 3))) .nil := by
  intro h
  cases h

end Solidity.Examples.DecisionFixedArrayPair
