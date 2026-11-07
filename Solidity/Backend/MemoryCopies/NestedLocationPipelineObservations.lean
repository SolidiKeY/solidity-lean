import Solidity.Backend.MemoryCopies.NestedLocationPipeline

/-! Runtime observations extracted from the composed allocator witnesses. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem nested_location_pipeline_observations {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot)
    (fits : cursor.val + 2 * nestedStorageParentDemand rows < W)
    (result : NestedLocationPipelineResult heap primitive rows bounded base frame cursor machine source fits)
    (positive : 0 < cursor.val) :
    ∃ target : Machine,
    run (nestedLocationPipelineCode primitive) (machine.push (.slot source)) =
      .ok (target.push (.val (wmod (cursor.val + nestedStorageParentDemand rows)))) 0 ∧
    target.mem 0 = .val (wmod (cursor.val + 2 * nestedStorageParentDemand rows)) ∧
    target.mem cursor.val = .val (wmod rows.length) ∧
    target.mem (cursor.val + nestedStorageParentDemand rows) = .val (wmod rows.length) ∧
    target.stack = machine.stack ∧ target.store = machine.store := by
  let value := nestedStorageParentValue primitive rows bounded
  let first := value.copyStToM heap rfl
  let snapshot := MVal.copyMToSt first.heap first.val
  let second := snapshot.copyStToM first.heap rfl
  obtain ⟨firstFits, base₁, intermediate, _, base₂, target, _, firstAllocator, firstRoot,
    _, ran, allocated, root, _, _, shape, _, retained, _, _, _, _, length, _, _⟩ := result
  have firstLength : first.heap.len first.val .dyn = rows.length := by
    simpa only [nestedStorageParentValue, SVal.view_array] using SVal.copyStToM_array_len heap value rfl
  have firstHeader : intermediate.mem cursor.val = .val (wmod rows.length) := by
    have cell : intermediate.mem (base₁ first.val.id).val = .val (wmod (first.heap.len first.val .dyn)) :=
      (firstAllocator.heap.arrays .dyn first.val).length rfl
    rw [firstRoot, firstLength] at cell
    exact cell
  have demandPositive : 0 < nestedStorageParentDemand rows := by
    simp only [nestedStorageParentDemand]
    omega
  have firstKept : target.mem cursor.val = .val (wmod rows.length) :=
    (retained cursor.val positive (by omega)).trans firstHeader
  have secondHeader : target.mem (cursor.val + nestedStorageParentDemand rows) = .val (wmod rows.length) := by
    have cell : target.mem (base₂ second.val.id).val = .val (wmod (second.heap.len second.val .dyn)) :=
      (allocated.heap.arrays .dyn second.val).length rfl
    rw [root, length] at cell
    exact cell
  have pointer : (⟨cursor.val + nestedStorageParentDemand rows, firstFits⟩ : Fin W) =
      wmod (cursor.val + nestedStorageParentDemand rows) := Fin.ext (Nat.mod_eq_of_lt firstFits).symm
  rw [pointer] at ran
  refine ⟨target, ran, allocated.free.cell.trans ?_, firstKept, secondHeader,
    (by rw [shape]), (by rw [shape])⟩
  apply congrArg Word.val
  exact Fin.ext (Nat.mod_eq_of_lt fits).symm

#print axioms nested_location_pipeline_observations
end Solidity.Backend.MemoryCopies
