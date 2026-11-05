import Solidity.Backend.MemoryCopies.NestedMemoryParent
import Solidity.Backend.MemoryCopies.NestedMemoryParentDemand
import Solidity.Backend.MemoryCopies.NestedMemoryMixedControls

/-! The existing mixed 2/0/64 producer supplies an actual represented source.
The new compiled entry loads its header and allocates/adopts a fresh parent. -/
namespace Solidity.Backend.MemoryCopies.NestedMemoryParentMixedControls
open Evm Evm.Memory

structure MixedParentWitness where
  input : NestedMemoryMixedControls.MixedRuntimeWitness
  totalCost : memoryParentDemand input.heap .uint input.source = 73
  fits : (wmod 113).val + memoryParentDemand input.heap .uint input.source < W
  copy : NestedMemoryParentResult input.heap .uint input.source input.base 8 (wmod 113) input.before fits

theorem mixed_parent_inhabited : Nonempty MixedParentWitness := by
  obtain ⟨input⟩ := NestedMemoryMixedControls.mixed_runtime
  have cost : memoryParentDemand input.heap .uint input.source = 73 := by
    rw [memory_parent_demand_snapshot, input.sourceSnapshot]
    decide +kernel
  have fits : (wmod 113).val + memoryParentDemand input.heap .uint input.source < W := by
    rw [cost]
    decide
  exact ⟨⟨input, cost, fits, nested_memory_parent_success input.heap .uint input.source input.base 8 (wmod 113)
    input.before input.allocator fits⟩⟩

theorem mixed_parent_runtime : ∃ witness : MixedParentWitness, ∃ target : Machine,
    run (nestedMemoryParentCode .uint) (witness.input.before.push w[40]) = .ok (target.push w[113]) 0 ∧
    target.mem 0 = w[186] ∧ target.mem 113 = w[3] := by
  obtain ⟨witness⟩ := mixed_parent_inhabited
  obtain ⟨base', target, ran, allocated, root, _, _, _, _, _, _, length, _, _⟩ := witness.copy
  let snapshot := MVal.copyMToSt witness.input.heap (T := .ref (.array (.ref (.array (.prim .uint))))) witness.input.source
  let grown := snapshot.copyStToM witness.input.heap rfl
  have cursorEq : (⟨(wmod 113).val + memoryParentDemand witness.input.heap .uint witness.input.source, witness.fits⟩ : Fin W) = (⟨186, by decide⟩ : Fin W) := by
    apply Fin.ext
    change (wmod 113).val + memoryParentDemand witness.input.heap .uint witness.input.source = 186
    rw [witness.totalCost]
    decide
  have cell : target.mem 0 = w[186] := by
    rw [← cursorEq]
    exact allocated.free.cell
  have header : target.mem (base' grown.val.id).val = .val (wmod (grown.heap.len grown.val .dyn)) :=
    (allocated.heap.arrays .dyn grown.val).length rfl
  rw [root, length, witness.input.sourceCount] at header
  rw [witness.input.sourceRoot] at ran
  exact ⟨witness, target, ran, cell, header⟩

#print axioms mixed_parent_inhabited
#print axioms mixed_parent_runtime
end Solidity.Backend.MemoryCopies.NestedMemoryParentMixedControls
