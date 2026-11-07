import Solidity.Backend.MemoryCopies.CheckedFixedStorageInterface

/-! The existing positive-cost guard executes before allocation and copying.
Every successful fixed-copy clause is transported without a new capacity premise. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem checked_fixed_storage_run (count : Nat) (machine : Machine) (cursor : Fin W) (source : Slot)
    (cell : machine.mem 0 = .val cursor) :
    run (checkedFixedStorageCode count) (machine.push (.slot source)) =
      if cursor.val + max 1 count < W
      then run (runtimeFixedStorageCode count) (machine.push (.slot source)) else .revert := by
  have guard : run (defaultCapacityGuard (max 1 count)) (machine.push (.slot source)) =
      if cursor.val + max 1 count < W then .ok (machine.push (.slot source)) 0 else .revert :=
    default_capacity_guard_run (max 1 count) (by omega) (machine.push (.slot source)) cursor cell
  rw [checkedFixedStorageCode]
  by_cases fits : cursor.val + max 1 count < W
  · rw [if_pos fits] at guard
    rw [run_append_ok guard,if_pos fits]
  · rw [if_neg fits] at guard
    rw [run_append_revert guard,if_neg fits]

theorem checked_fixed_storage_success {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (value : SVal (.ref (.fixed (.prim primitive) count))) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (source : Slot) (limit : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store limit (.ref (.fixed (.prim primitive) count)) source value)
    (fits : cursor.val + max 1 count < W) :
    CheckedFixedStorageResult heap primitive count value base frame cursor machine source fits := by
  obtain ⟨base',target,ran,allocated,rootAt,extension,shape,below,gaps,keeps,fresh⟩ :=
    runtime_fixed_storage_success heap primitive count value base frame cursor machine source limit allocator represented fits
  refine ⟨base',target,?_,allocated,rootAt,extension,shape,below,gaps,keeps,fresh⟩
  rw [checked_fixed_storage_run count machine cursor source allocator.free.cell,if_pos fits]
  exact ran

theorem checked_fixed_storage_correct {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (value : SVal (.ref (.fixed (.prim primitive) count))) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (source : Slot) (limit : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store limit (.ref (.fixed (.prim primitive) count)) source value) :
    (∃ fits, CheckedFixedStorageResult heap primitive count value base frame cursor machine source fits) ∨
    (¬ cursor.val + max 1 count < W ∧ run (checkedFixedStorageCode count) (machine.push (.slot source)) = .revert) := by
  by_cases fits : cursor.val + max 1 count < W
  · exact Or.inl ⟨fits,checked_fixed_storage_success heap primitive count value base frame cursor machine source limit allocator represented fits⟩
  · right
    refine ⟨fits,?_⟩
    rw [checked_fixed_storage_run count machine cursor source allocator.free.cell,if_neg fits]

/-- Code-level refusal for an unrepresentable reservation demand. This theorem
requires no inhabited fixed value and makes no Source admission claim. -/
theorem checked_fixed_storage_large_code (count : Nat) (large : W ≤ max 1 count)
    (machine : Machine) (cursor : Fin W) (source : Slot) (cell : machine.mem 0 = .val cursor) :
    run (checkedFixedStorageCode count) (machine.push (.slot source)) = .revert := by
  rw [checked_fixed_storage_run count machine cursor source cell,if_neg (by omega)]

def checkedFixedStorage : CheckedFixedStorageCertificate := ⟨checked_fixed_storage_correct⟩

#print axioms checked_fixed_storage_run
#print axioms checked_fixed_storage_success
#print axioms checked_fixed_storage_correct
#print axioms checked_fixed_storage_large_code
#print axioms checkedFixedStorage
end Solidity.Backend.MemoryCopies
