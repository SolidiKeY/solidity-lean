import Solidity.Backend.MemoryCopies.CheckedDefault
import Solidity.Evm.MemoryObjectArrayExamples

/-! Selected nested defaults remain inhabited without fitting witnesses.
Actual capacity refusal and unused huge children are distinct from failure. -/
namespace Solidity.Backend.MemoryCopies.CheckedDefaultControls
open Evm Evm.Memory
private def element : Ty := .ref (.array (.prim .uint))
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_,_,_,_,ObjectArrayExamples.initial_allocator⟩
private def selected (dimensions : List Nat) :
    SelectedCheckedDefault (nestedArrayType element dimensions) (nested_mapFree element dimensions) :=
  checkedNestedDefault element dimensions (nested_mapFree element dimensions)
private def observe : Evm.Out → Option (Nat × Nat × Nat)
  | .ok machine _ => match machine.stack,machine.mem 0,machine.mem 17 with
    | .val root :: _,.val cursor,.val old => some (root.val,cursor.val,old.val)
    | _,_,_ => none
  | _ => none

theorem certificate_inhabited : CheckedDefaultCertificate := checkedDefault

theorem selected_observation (dimensions : List Nat)
    (fits : 40 + ReferenceDefaults.defaultCells (.ref (nestedArrayType element dimensions)) < W) :
    observe (run (selected dimensions).code input.machine) =
      some (40,40 + ReferenceDefaults.defaultCells (.ref (nestedArrayType element dimensions)),7) := by
  obtain ⟨base,target,ran,allocated,_,_,_,below,_⟩ :=
    (selected dimensions).success input.heap input.base 8 (wmod 40) input.machine input.allocator fits
  rw [ran]
  simp only [observe,Machine.push]
  rw [allocated.free.cell,below 17 (by decide) (by decide)]
  rfl

theorem empty_dynamic : observe (run (selected []).code input.machine) = some (40,41,7) :=
  selected_observation [] (by decide)

theorem nested_two_three : observe (run (selected [2,3]).code input.machine) = some (40,54,7) :=
  selected_observation [2,3] (by decide)

theorem long_dimension : observe (run (selected [1,64]).code input.machine) = some (40,169,7) :=
  selected_observation [1,64] (by decide)

theorem unfittable_selected : Nonempty (SelectedCheckedDefault (nestedArrayType element [W]) (nested_mapFree element [W])) :=
  ⟨selected [W]⟩

private theorem large_cost : W ≤ ReferenceDefaults.defaultCells (.ref (nestedArrayType element [W])) := by
  change W ≤ max 1 W + W * 1
  omega

theorem unfittable_refusal : run (selected [W]).code input.machine = .revert := by
  rw [(selected [W]).run_checked input.heap input.base 8 (wmod 40) input.machine input.allocator]
  apply if_neg
  have demand : W ≤ ReferenceDefaults.defaultCells (.ref (nestedArrayType element [W])) := large_cost
  omega

theorem unused_huge_child : observe (run (selected [0,W]).code input.machine) = some (40,41,7) := by
  apply selected_observation [0,W]
  change 40 + (max 1 0 + 0 * (max 1 W + W * 1)) < W
  have large : 41 < W := by decide
  omega

theorem empty_code_rejected : (selected [2,3]).code ≠ [] := by
  intro empty
  have observed : observe (run (selected [2,3]).code input.machine) = some (40,54,7) := nested_two_three
  rw [empty] at observed
  have actual : observe (run [] input.machine) = some (77,40,7) := by rfl
  rw [actual] at observed
  cases observed

theorem refusal_not_success : observe (run (selected [W]).code input.machine) = none := by
  rw [unfittable_refusal]
  rfl

theorem wrong_cursor_rejected : observe (run (selected [2,3]).code input.machine) ≠ some (40,55,7) := by
  rw [nested_two_three]
  decide

theorem static_capacity_refusal (machine : Machine) (cost : Nat) (tooLarge : W ≤ cost) :
    run (defaultCapacityGuard cost) machine = .revert := by
  simp only [defaultCapacityGuard,if_neg (by omega : ¬ cost < W),run,exec_cons_zero,Instr.step,Out.revert_bind]

theorem exact_boundary_refusal (machine : Machine) (cell : machine.mem 0 = .val wMax) :
    run (defaultCapacityGuard 1) machine = .revert := by
  rw [default_capacity_guard_run 1 (by decide) machine wMax cell]
  apply if_neg
  change ¬ (W - 1 + 1 < W)
  have positive : 0 < W := W_pos
  omega

#print axioms certificate_inhabited
#print axioms selected_observation
#print axioms empty_dynamic
#print axioms nested_two_three
#print axioms long_dimension
#print axioms unfittable_selected
#print axioms unfittable_refusal
#print axioms unused_huge_child
#print axioms empty_code_rejected
#print axioms refusal_not_success
#print axioms wrong_cursor_rejected
#print axioms static_capacity_refusal
#print axioms exact_boundary_refusal
end Solidity.Backend.MemoryCopies.CheckedDefaultControls
