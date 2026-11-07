import Solidity.Backend.MemoryCopies.CheckedFixedMemoryInterface

/-! A positive reservation guard runs before the existing fixed memory loop.
Successful execution transports every prior heap and allocator guarantee. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem checked_fixed_memory_run (count : Nat) (machine : Machine) (cursor source : Fin W)
    (cell : machine.mem 0 = .val cursor) :
    run (checkedFixedMemoryCode count) (machine.push (.val source)) =
      if cursor.val + max 1 count < W
      then run (runtimeFixedMemoryCode count) (machine.push (.val source)) else .revert := by
  have guard : run (defaultCapacityGuard (max 1 count)) (machine.push (.val source)) =
      if cursor.val + max 1 count < W then .ok (machine.push (.val source)) 0 else .revert :=
    default_capacity_guard_run (max 1 count) (by omega) (machine.push (.val source)) cursor cell
  rw [checkedFixedMemoryCode]
  by_cases fits : cursor.val + max 1 count < W
  · rw [if_pos fits] at guard
    rw [run_append_ok guard,if_pos fits]
  · rw [if_neg fits] at guard
    rw [run_append_revert guard,if_neg fits]

theorem checked_fixed_memory_success {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (input : HRef H (.fixed (.prim primitive) count)) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (fits : cursor.val + max 1 count < W) :
    CheckedFixedMemoryResult heap primitive count input base frame cursor machine fits := by
  obtain ⟨base',target,ran,allocated,rootAt,extension,shape,below,gaps,keeps,fresh⟩ :=
    runtime_fixed_memory_success heap primitive count input base frame cursor machine allocator fits
  refine ⟨base',target,?_,allocated,rootAt,extension,shape,below,gaps,keeps,fresh⟩
  rw [checked_fixed_memory_run count machine cursor (base input.id) allocator.free.cell,if_pos fits]
  exact ran

theorem checked_fixed_memory_correct {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (input : HRef H (.fixed (.prim primitive) count)) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    (∃ fits, CheckedFixedMemoryResult heap primitive count input base frame cursor machine fits) ∨
    (¬ cursor.val + max 1 count < W ∧
      run (checkedFixedMemoryCode count) (machine.push (.val (base input.id))) = .revert) := by
  by_cases fits : cursor.val + max 1 count < W
  · exact Or.inl ⟨fits,checked_fixed_memory_success heap primitive count input base frame cursor machine allocator fits⟩
  · right
    refine ⟨fits,?_⟩
    rw [checked_fixed_memory_run count machine cursor (base input.id) allocator.free.cell,if_neg fits]

/-- Code-only oversized reservation refusal; no giant represented object or
Source admission is inferred from this execution fact. -/
theorem checked_fixed_memory_large_code (count : Nat) (large : W ≤ max 1 count)
    (machine : Machine) (cursor source : Fin W) (cell : machine.mem 0 = .val cursor) :
    run (checkedFixedMemoryCode count) (machine.push (.val source)) = .revert := by
  rw [checked_fixed_memory_run count machine cursor source cell,if_neg (by omega)]

def checkedFixedMemory : CheckedFixedMemoryCertificate := ⟨checked_fixed_memory_correct⟩

#print axioms checked_fixed_memory_run
#print axioms checked_fixed_memory_success
#print axioms checked_fixed_memory_correct
#print axioms checked_fixed_memory_large_code
#print axioms checkedFixedMemory
end Solidity.Backend.MemoryCopies
