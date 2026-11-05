import Solidity.Calculus.DecisionFixedArrayPath
import Solidity.Examples.FixedArrayFloor

/-! # Inhabited fixed-array reconstruction below typed arrayPrefixes
These controls exercise actual lookup/save values, without changing coverage.
-/
namespace Solidity.Examples.DecisionFixedArrayPath
open Solidity.Decide
set_option Elab.async false

def inner : SVal (.ref (.fixed (.prim .uint) 3)) :=
  .fixed FixedArrayFloor.original

def nested : SVal (.ref (.fixed (.ref (.fixed (.prim .uint) 3)) 2)) :=
  .fixed (.cons inner (.cons inner .nil))

def arrayPrefix : Path (.ref (.fixed (.ref (.fixed (.prim .uint) 3)) 2))
    (.ref (.fixed (.prim .uint) 3)) := .atF (uintOfNat 1) .nil

theorem selected_present : nested.findM arrayPrefix = some inner := by decide +kernel

theorem nested_reconstruction : ∃ x', fixedFloorAtPath arrayPrefix [2, 3] nested = some x' :=
  fixedFloorAtPath_exists arrayPrefix [2, 3] nested selected_present

theorem nested_changed : ∃ x', fixedFloorAtPath arrayPrefix [2, 3] nested = some x' ∧
    x'.findM (.atF (uintOfNat 1) (.atF (uintOfNat 1) .nil)) =
      some (.prim (uintOfNat 7)) := by decide +kernel

theorem nested_old_read : nested.findM
    (.atF (uintOfNat 1) (.atF (uintOfNat 1) .nil)) = some (.prim (uintOfNat 9)) := by
  decide +kernel

theorem nested_outside : fixedFloorAtPath
    (.atF (uintOfNat 2) .nil) [2, 3] nested = none := by decide +kernel

def mapping : SVal (.ref (.mapping .uint (.ref (.fixed (.prim .uint) 3)))) :=
  .map (.cons (uintOfNat 5) inner .nil) inner

def keyPrefix : Path (.ref (.mapping .uint (.ref (.fixed (.prim .uint) 3))))
    (.ref (.fixed (.prim .uint) 3)) := .key (uintOfNat 5) .nil

theorem mapping_present : mapping.findM keyPrefix = some inner := by decide +kernel

theorem mapping_changed : ∃ x', fixedFloorAtPath keyPrefix [2, 3] mapping = some x' ∧
    x'.findM (.key (uintOfNat 5) (.atF (uintOfNat 1) .nil)) =
      some (.prim (uintOfNat 7)) := by decide +kernel

theorem mapping_other_key : ∃ x', fixedFloorAtPath keyPrefix [2, 3] mapping = some x' ∧
    x'.findM (.key (uintOfNat 6) (.atF (uintOfNat 1) .nil)) =
      mapping.findM (.key (uintOfNat 6) (.atF (uintOfNat 1) .nil)) := by decide +kernel

theorem missing_length_not_silent : ∃ x', fixedFloorAtPath arrayPrefix [] nested = some x' ∧
    x'.findM (.atF (uintOfNat 1) (.atF (uintOfNat 3) .nil)) = none ∧
    nested.findM (.atF (uintOfNat 1) (.atF (fixedFloorIndex [] (uintOfNat 3)) .nil)) =
      some (.prim (uintOfNat 7)) := by decide +kernel

end Solidity.Examples.DecisionFixedArrayPath
