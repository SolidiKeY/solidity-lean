import Solidity.Calculus.FixedArrayFloor

/-! # Inhabited fixed storage-floor controls
These kernel controls do not promote array decision coverage. -/
namespace Solidity.Examples.FixedArrayFloor
open Solidity.Decide
set_option Elab.async false

def original : SVec (.prim .uint) 3 :=
  .cons (.prim (uintOfNat 7))
    (.cons (.prim (uintOfNat 9)) (.cons (.prim (uintOfNat 11)) .nil))

def rebuilt : SVec (.prim .uint) 3 := fixedFloorVec [2, 3] original

theorem interior_changes : rebuilt.toList[1]? = some (.prim (uintOfNat 7)) := by
  decide +kernel

theorem interior_changed : rebuilt.toList[1]? ≠ original.toList[1]? := by
  decide +kernel

theorem retained_read : rebuilt.toList[2]? = original.toList[2]? :=
  fixedFloorVec_at [2, 3] original (by decide) (by decide)

theorem length_read_halts : rebuilt.toList[3]? = none := by decide +kernel

theorem past_length_halts : rebuilt.toList[4]? = none := by decide +kernel

/-- A decreasing floor alone cannot preserve absence beyond a fixed length. -/
theorem missing_length_changes_definedness :
    (fixedFloorVec [] original).toList[3]? = none ∧
      original.toList[mxFloorIndex [] 3]? = some (.prim (uintOfNat 7)) := by
  decide +kernel

theorem missing_length_invalidates_slot_identity :
    (fixedFloorVec [] original).toList[3]? ≠ original.toList[mxFloorIndex [] 3]? := by
  decide +kernel

def empty : SVec (.prim .bool) 0 := .nil

theorem empty_halts (k : Nat) : (fixedFloorVec [0] empty).toList[k]? = none := by
  exact List.getElem?_eq_none (by rw [fixedFloorVec_length]; omega)

/-- The element is itself an array, retaining its intrinsic reference type. -/
def nested : SVec (.ref (.fixed (.prim .uint) 2)) 2 :=
  .cons (.fixed (.cons (.prim (uintOfNat 7)) (.cons (.prim (uintOfNat 9)) .nil)))
    (.cons (.fixed (.cons (.prim (uintOfNat 11)) (.cons (.prim (uintOfNat 13)) .nil))) .nil)

theorem nested_path_read :
    (SVal.fixed (fixedFloorVec [0, 2] nested)).findM
      (.atF (uintOfNat 1) (.atF (uintOfNat 1) .nil)) = some (.prim (uintOfNat 9)) := by
  decide +kernel

/-- The general storage-path theorem applies to a nontrivial continuation. -/
theorem nested_path_bridge :
    (SVal.fixed (fixedFloorVec [0, 2] nested)).findM
      (.atF (uintOfNat 1) (.atF (uintOfNat 1) .nil)) =
    (SVal.fixed nested).findM
      (.atF (fixedFloorIndex [0, 2] (uintOfNat 1)) (.atF (uintOfNat 1) .nil)) :=
  fixedFloorVec_find [0, 2] nested (by decide) _ _

def boolInput : SVec (.prim .bool) 2 :=
  .cons (.prim true) (.cons (.prim false) .nil)

theorem bool_input_not_block :
    ¬ (∀ k : Nat, k < 2 → boolInput.toList[k]? = some (.prim true)) := by
  intro h
  have hf : boolInput.toList[1]? = some (.prim true) := h 1 (by decide)
  have hn : boolInput.toList[1]? ≠ some (.prim true) := by decide +kernel
  exact hn hf

/-- A genuinely different vector realizes all the finite block's instances. -/
theorem bool_rebuilt_block : ∀ k : Nat, k < 2 →
    (fixedFloorVec [0, 2] boolInput).toList[k]? = some (.prim true) := by
  intro k hk
  have he : k = 0 ∨ k = 1 := by omega
  rcases he with rfl | rfl <;> decide +kernel

/-- Inhabited Boolean specialization: the finite premise checks only index zero. -/
theorem bool_finite_boundary :
    (∀ v : SVec (.prim .bool) 2,
      (∀ k : Nat, k < 2 → v.toList[k]? = some (.prim true)) →
      [v.toList[0]?] = [some (.prim true)]) ↔
    (∀ v : SVec (.prim .bool) 2,
      (∀ k : Nat, k = 0 ∨ (k : Int) ∈ [0, 2] → k < 2 →
        v.toList[k]? = some (.prim true)) →
      [v.toList[0]?] = [some (.prim true)]) :=
  fixedFloorVec_negative_iff (E := .prim .bool) (n := 2)
    (fun _ => [0, 2]) [0] (fun _ => List.mem_cons_of_mem _ List.mem_cons_self)
    (fun _ k hk => by
      simp only [List.mem_singleton] at hk
      subst k
      exact List.mem_cons_self)
    (fun x => x = some (.prim true)) (fun xs => xs = [some (.prim true)])

end Solidity.Examples.FixedArrayFloor
