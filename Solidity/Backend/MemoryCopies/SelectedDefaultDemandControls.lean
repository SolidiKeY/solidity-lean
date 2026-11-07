import Solidity.Backend.MemoryCopies.SelectedDefaultDemand
import Solidity.Evm.MemoryObjectArrayExamples
import Solidity.Backend.MemoryCopies.HeapContents

/-! Inhabited selected defaults, unused large children and actual size refusal.
Unselected reference structs are a negative control, not an approved-domain exclusion. -/
namespace Solidity.Backend.MemoryCopies.SelectedDefaultDemandControls
open Evm Evm.Memory

private def element : Ty := .ref (.array (.prim .uint))
private def chosen (dimensions : List Nat) :
    SelectedCheckedDefault (nestedArrayType element dimensions) (nested_mapFree element dimensions) :=
  checkedNestedDefault element dimensions (nested_mapFree element dimensions)
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_, _, _, _, ObjectArrayExamples.initial_allocator⟩
private def observe : Evm.Out → Option (Nat × Nat × Nat)
  | .ok machine _ => match machine.stack, machine.mem 0, machine.mem 17 with
    | .val root :: _, .val cursor, .val old => some (root.val, cursor.val, old.val)
    | _, _, _ => none
  | _ => none

theorem certificate_inhabited : SelectedDefaultDemandCertificate := selectedDefaultDemand

theorem nested_actual_demand (dimensions : List Nat) :
    heapWords (input.heap.allocDefault (nestedArrayType element dimensions)
      (nested_mapFree element dimensions)).heap = heapWords input.heap +
        liveWordCount (SVal.dflt (.ref (nestedArrayType element dimensions))) :=
  default_allocation_words input.heap _ _

private theorem chosen_words (dimensions : List Nat) :
    liveWordCount (SVal.dflt (.ref (nestedArrayType element dimensions))) =
      ReferenceDefaults.defaultCells (.ref (nestedArrayType element dimensions)) :=
  selected_default_words _ _ (by rw [(chosen dimensions).selected]; rfl)

theorem selected_demands :
    liveWordCount (SVal.dflt (.ref (nestedArrayType element []))) = 1 ∧
    liveWordCount (SVal.dflt (.ref (nestedArrayType element [2,3]))) = 14 ∧
    liveWordCount (SVal.dflt (.ref (nestedArrayType element [1,64]))) = 129 ∧
    liveWordCount (SVal.dflt (.ref (nestedArrayType element [0,W]))) = 1 := by
  rw [chosen_words [], chosen_words [2,3], chosen_words [1,64], chosen_words [0,W]]
  decide +kernel

theorem unselected_struct_control :
    ReferenceDefaults.compileDefault (.struct "Account") rfl = none ∧
    liveWordCount (SVal.dflt (.ref (.struct "Account"))) = 3 ∧
    ReferenceDefaults.defaultCells (.ref (.struct "Account")) = 2 := by
  refine ⟨rfl, ?_, rfl⟩
  decide +kernel

theorem selected_primitive_struct :
    (ReferenceDefaults.compileDefault (.struct "Token") rfl).isSome = true ∧
    liveWordCount (SVal.dflt (.ref (.struct "Token"))) = 1 := by decide +kernel

theorem actual_success (dimensions : List Nat)
    (fits : 40 + liveWordCount (SVal.dflt (.ref (nestedArrayType element dimensions))) < W) :
    observe (run (chosen dimensions).code input.machine) =
      some (40, 40 + liveWordCount (SVal.dflt (.ref (nestedArrayType element dimensions))), 7) := by
  have available : (ReferenceDefaults.compileDefault (nestedArrayType element dimensions)
      (nested_mapFree element dimensions)).isSome = true := by rw [(chosen dimensions).selected]; rfl
  rw [selected_default_words _ _ available] at fits ⊢
  obtain ⟨base, target, ran, allocated, _, _, _, below, _⟩ :=
    (chosen dimensions).success input.heap input.base 8 (wmod 40) input.machine input.allocator fits
  rw [ran]
  simp only [observe, Machine.push]
  rw [allocated.free.cell, below 17 (by decide) (by decide)]
  rfl

theorem actual_mixed : observe (run (chosen [2,3]).code input.machine) = some (40,54,7) :=
  actual_success [2,3] (by decide +kernel)

private def emptyChild : SVal (.ref (.array element)) := .array .nil .nil (by decide)
private def expectedChildren : SVal (.ref (nestedArrayType element [2,3])) :=
  .fixed (SVec.replicate (.fixed (SVec.replicate emptyChild 3)) 2)

/-- The full actual execution/allocator witness carries the represented heap
whose snapshot has both fixed rows and all six empty dynamic children. -/
theorem actual_new_children :
    ∃ fits : (wmod 40).val + ReferenceDefaults.defaultCells (.ref (nestedArrayType element [2,3])) < W,
      Objects.DefaultBuildResult input.heap (nestedArrayType element [2,3])
        (nested_mapFree element [2,3]) (chosen [2,3]).code
        (ReferenceDefaults.defaultCells (.ref (nestedArrayType element [2,3])))
        input.base 8 (wmod 40) input.machine fits ∧
      let grown := input.heap.allocDefault (nestedArrayType element [2,3]) (nested_mapFree element [2,3])
      MVal.copyMToSt grown.heap grown.val = expectedChildren := by
  refine ⟨by decide, (chosen [2,3]).success input.heap input.base 8 (wmod 40)
    input.machine input.allocator (by decide), ?_⟩
  exact ((storageHeapContents (SVal.dflt (.ref (nestedArrayType element [2,3])))
    (nested_mapFree element [2,3])).contents input.heap).trans (by
      simp only [nestedArrayType, SVal.dflt_fixed, SVal.dflt_array, SVal.strip_fixed,
        SVal.strip_array, SVec.strip_cons, SVec.strip_nil, SVec.replicate, expectedChildren, emptyChild])

theorem unused_huge_child : observe (run (chosen [0,W]).code input.machine) = some (40,41,7) := by
  have fits : 40 + liveWordCount (SVal.dflt (.ref (nestedArrayType element [0,W]))) < W := by
    rw [chosen_words [0,W]]
    decide +kernel
  have actual : observe (run (chosen [0,W]).code input.machine) =
      some (40,40 + liveWordCount (SVal.dflt (.ref (nestedArrayType element [0,W]))),7) :=
    actual_success [0,W] fits
  rw [chosen_words [0,W]] at actual
  exact actual


theorem actual_refusal : run (chosen [W]).code input.machine = .revert := by
  rw [(chosen [W]).run_checked input.heap input.base 8 (wmod 40) input.machine input.allocator]
  apply if_neg
  change ¬ 40 + (max 1 W + W * 1) < W
  omega

theorem wrong_cursor_rejected : observe (run (chosen [2,3]).code input.machine) ≠ some (40,55,7) := by
  rw [actual_mixed]
  decide

/--
info: 'Solidity.Backend.MemoryCopies.SelectedDefaultDemandControls.certificate_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms certificate_inhabited
/--
info: 'Solidity.Backend.MemoryCopies.SelectedDefaultDemandControls.selected_demands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms selected_demands
/--
info: 'Solidity.Backend.MemoryCopies.SelectedDefaultDemandControls.unselected_struct_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms unselected_struct_control
/--
info: 'Solidity.Backend.MemoryCopies.SelectedDefaultDemandControls.selected_primitive_struct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms selected_primitive_struct
/--
info: 'Solidity.Backend.MemoryCopies.SelectedDefaultDemandControls.actual_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_success
/--
info: 'Solidity.Backend.MemoryCopies.SelectedDefaultDemandControls.actual_mixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_mixed
/--
info: 'Solidity.Backend.MemoryCopies.SelectedDefaultDemandControls.actual_new_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_new_children
/--
info: 'Solidity.Backend.MemoryCopies.SelectedDefaultDemandControls.unused_huge_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms unused_huge_child
/--
info: 'Solidity.Backend.MemoryCopies.SelectedDefaultDemandControls.actual_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_refusal
/--
info: 'Solidity.Backend.MemoryCopies.SelectedDefaultDemandControls.wrong_cursor_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms wrong_cursor_rejected
end Solidity.Backend.MemoryCopies.SelectedDefaultDemandControls
