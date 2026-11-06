import Solidity.Backend.MemoryCopies.NestedDefaults
import Solidity.Evm.MemoryObjectArrayExamples

/-! Actual compiled default observations over a populated represented heap.
Loop execution follows the existing checked builder simulation, not evaluation
of the noncomputable target loop definition. No target run is a premise. -/
namespace Solidity.Backend.MemoryCopies.NestedDefaultControls
open Evm Evm.Memory

private def element : Ty := .ref (.array (.prim .uint))
private def feasible {cost : Nat} (fits : 40 + cost < W) : V2.AllocatorWitness cost :=
  ⟨_, _, _, 8, ⟨40, by decide⟩, _, ObjectArrayExamples.initial_allocator, fits⟩
private def machine : Machine := (feasible (cost := 1) (by decide)).machine
private def selected (dimensions : List Nat)
    (fits : 40 + ReferenceDefaults.defaultCells (.ref (nestedArrayType element dimensions)) < W) :
    SelectedNestedDefault element dimensions (nested_mapFree element dimensions) :=
  selectedNestedDefault element dimensions (nested_mapFree element dimensions) (feasible fits)

private def observe : Evm.Out → Option (Nat × Nat × Nat)
  | .ok machine _ => match machine.stack, machine.mem 0, machine.mem 17 with
    | .val root :: _, .val cursor, .val old => some (root.val, cursor.val, old.val)
    | _, _, _ => none
  | _ => none

/-- Actual selected code returns the old cursor, advances its exact demand,
and leaves a populated old object's live word unchanged. -/
theorem selected_observation (dimensions : List Nat)
    (fits : 40 + ReferenceDefaults.defaultCells (.ref (nestedArrayType element dimensions)) < W) :
    observe (run (selected dimensions fits).certified.builder.code machine) =
      some (40, 40 + ReferenceDefaults.defaultCells (.ref (nestedArrayType element dimensions)), 7) := by
  let chosen : SelectedNestedDefault element dimensions (nested_mapFree element dimensions) :=
    selected dimensions fits
  let input : V2.AllocatorWitness (ReferenceDefaults.defaultCells
      (.ref (nestedArrayType element dimensions))) := chosen.certified.feasible
  obtain ⟨base, target, execution, represented, _, _, _, preserved, _⟩ :=
    chosen.execute input.heap input.base input.frame input.cursor input.machine input.represented input.fits
  change observe (run chosen.certified.builder.code input.machine) = _
  rw [execution]
  simp only [observe, Machine.push]
  rw [represented.free.cell, preserved 17 (by decide) (by change 17 < 40; decide)]
  rfl

theorem empty_reference_array :
    observe (run (selected [] (by decide)).certified.builder.code machine) =
      some (40,41,7) := selected_observation [] (by decide)

theorem nested_two_three :
    observe (run (selected [2,3] (by decide)).certified.builder.code machine) =
      some (40,54,7) := selected_observation [2,3] (by decide)

theorem long_dimension :
    observe (run (selected [1,64] (by decide)).certified.builder.code machine) =
      some (40,169,7) := selected_observation [1,64] (by decide)

theorem nested_inhabited : Nonempty (SelectedNestedDefault element [2,3] rfl) :=
  ⟨selected [2,3] (by decide)⟩

theorem empty_code_rejected : (selected [2,3] (by decide)).certified.builder.code ≠ [] :=
  (selected [2,3] (by decide)).code_ne_nil

theorem wrong_cursor_rejected :
    observe (run (selected [2,3] (by decide)).certified.builder.code machine) ≠
      some (40,55,7) := by
  rw [nested_two_three]
  decide

#print axioms selected_observation
#print axioms empty_reference_array
#print axioms nested_two_three
#print axioms long_dimension
#print axioms nested_inhabited
#print axioms empty_code_rejected
#print axioms wrong_cursor_rejected
end Solidity.Backend.MemoryCopies.NestedDefaultControls
