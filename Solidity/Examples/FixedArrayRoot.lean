import Solidity.Calculus.FixedArrayRoot
import Solidity.Examples.FixedArrayFloor
import Solidity.Examples.DecisionArrayGaps

/-! # Fixed storage-root agreement controls
The decision pipeline and its gap observations remain unchanged. -/
namespace Solidity.Examples.FixedArrayRoot
open Solidity.Decide
open Solidity.Examples.DecisionArrayGaps (Probe)
set_option Elab.async false

private theorem fixedType : Probe.rootType "fixedArr" =
    some (.ref (.fixed (.prim .uint) 3)) := by decide +kernel
private theorem rowsType : Probe.rootType "fixedRows" =
    some (.ref (.mapping .uint (.ref (.fixed (.prim .uint) 3)))) := by decide +kernel

def sentinel : SVal (.ref (.mapping .uint (.ref (.fixed (.prim .uint) 3)))) :=
  .map (SMap.ofList [(uintOfNat 5, .fixed FixedArrayFloor.original)])
    (SVal.dflt (.ref (.fixed (.prim .uint) 3)))

def original : State Probe [] :=
  (State.init Probe).withStorage
    (((Storage.init Probe).set rowsType sentinel).set fixedType (.fixed FixedArrayFloor.original))

def rebuilt : State Probe [] := fixedFloorState fixedType [2, 3] original

theorem changed_root_word : rebuilt.storage.obs.word
    (.ref ⟨"fixedArr", fixedType, .atF (uintOfNat 1) .nil⟩) = uintOfNat 7 := by
  decide +kernel

theorem retained_root_word : rebuilt.storage.obs.word
    (.ref ⟨"fixedArr", fixedType, .atF (uintOfNat 2) .nil⟩) = uintOfNat 11 := by
  decide +kernel

theorem halted_root_read : rebuilt.storage.obs.has
    (.ref ⟨"fixedArr", fixedType, .atF (uintOfNat 3) .nil⟩) = false := by
  decide +kernel

/-- A non-default mapping entry at another root survives. -/
theorem sentinel_word : rebuilt.storage.obs.word
    (.ref ⟨"fixedRows", rowsType, .key (uintOfNat 5) (.atF (uintOfNat 1) .nil)⟩) =
      uintOfNat 9 := by
  decide +kernel

theorem sentinel_root_preserved : rebuilt.storage.get rowsType = original.storage.get rowsType :=
  fixedFloorRoot_get_ne fixedType [2, 3] original.storage rowsType (by decide)

/-- This retained typed storage observation is justified by the general agreement proof. -/
theorem retained_path_agreement :
    (rebuilt.storage.get fixedType).findM (.atF (uintOfNat 2) .nil) =
      (original.storage.get fixedType).findM (.atF (uintOfNat 2) .nil) :=
  fixedFloorRoot_retained fixedType [2, 3] original.storage (by decide) _ (by decide) _

def changedFormula : Fml Probe [] := dl[Probe]{ fixedArr[1] = 9 }

/-- Whole-formula agreement cannot be asserted for unretained reads. -/
theorem unretained_formula_changes : holds original changedFormula ∧ ¬ holds rebuilt changedFormula := by
  constructor
  · exact (holds_eq_of_eval (x := uintOfNat 9) (y := uintOfNat 9)
      (by decide +kernel) (by decide +kernel)).mpr rfl
  · intro h
    have he : uintOfNat 7 = uintOfNat 9 :=
      (holds_eq_of_eval (by decide +kernel) (by decide +kernel)).mp h
    exact (by decide +kernel : uintOfNat 7 ≠ uintOfNat 9) he

end Solidity.Examples.FixedArrayRoot
