import Solidity.Backend.MemoryCopies.CheckedStorageArrayInterface

/-! Storage length and free cursor are read before any copied write. The
existing storage copy supplies exact fresh contents and complete ownership. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem storage_capacity_guard_run (machine : Machine) (source : Slot) (cursor size : Fin W)
    (cell : machine.mem 0 = .val cursor) (header : machine.store.cells source = size) :
    run storageArrayCapacityGuard (machine.push (.slot source)) =
      if cursor.val + (size.val + 1) < W then .ok (machine.push (.slot source)) 0 else .revert := by
  have largest : W - 1 < W := by have positive : 0 < W := W_pos; omega
  have remaining : (W - 1 + (W - cursor.val)) % W = W - 1 - cursor.val := capacity_remaining cursor
  have bounded : cursor.val < W := cursor.isLt
  by_cases fits : cursor.val + (size.val + 1) < W
  · have comparison : size.val < W - 1 - cursor.val := by omega
    simp only [storageArrayCapacityGuard,assertTop,List.cons_append,List.nil_append,run,exec_cons_zero,
      Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,Nat.reduceSub,List.getElem?_cons_zero,
      cell,header,wmod_def,Nat.mod_eq_of_lt largest,remaining,comparison,decide_true,
      bword,↓reduceIte,
      Nat.succ_ne_self,exec_cons_succ,if_pos fits]
  · have comparison : ¬ size.val < W - 1 - cursor.val := by omega
    simp only [storageArrayCapacityGuard,assertTop,List.cons_append,List.nil_append,run,exec_cons_zero,
      Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,Nat.reduceSub,List.getElem?_cons_zero,
      cell,header,wmod_def,Nat.mod_eq_of_lt largest,remaining,comparison,decide_false,
      bword,Bool.false_eq_true,↓reduceIte,
      if_neg fits,Out.revert_bind]

theorem checked_storage_array_run {H : HTy} (heap : Heap H) (primitive : PrimTy) (values : List primitive.Denote)
    (bounded : values.length < W) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.prim primitive))) source (primitiveArrayValue primitive values bounded)) :
    run checkedStorageArrayCode (machine.push (.slot source)) =
      if cursor.val + (values.length + 1) < W then run runtimeStorageArrayCode (machine.push (.slot source)) else .revert := by
  obtain ⟨header,_,_⟩ := storage_array_words primitive values bounded machine source L represented
  have guard : run storageArrayCapacityGuard (machine.push (.slot source)) =
      if cursor.val + (values.length + 1) < W then .ok (machine.push (.slot source)) 0 else .revert := by
    simpa only [wmod_def,Nat.mod_eq_of_lt bounded] using
      storage_capacity_guard_run machine source cursor (wmod values.length) allocator.free.cell header
  rw [checkedStorageArrayCode]
  by_cases fits : cursor.val + (values.length + 1) < W
  · rw [if_pos fits] at guard
    rw [run_append_ok guard,if_pos fits]
  · rw [if_neg fits] at guard
    rw [run_append_revert guard,if_neg fits]

theorem checked_storage_array_success {H : HTy} (heap : Heap H) (primitive : PrimTy) (values : List primitive.Denote)
    (bounded : values.length < W) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.prim primitive))) source (primitiveArrayValue primitive values bounded))
    (fits : cursor.val + (values.length + 1) < W) :
    CheckedStorageArrayResult heap primitive values bounded base frame cursor machine source fits := by
  obtain ⟨base',target,ran,allocated,root,extension,shape,below,gaps⟩ :=
    runtime_storage_array_success heap primitive values bounded base frame cursor machine source L allocator represented fits
  refine ⟨base',target,?_,allocated,root,extension,shape,below,gaps⟩
  rw [checked_storage_array_run heap primitive values bounded base frame cursor machine source L allocator represented,if_pos fits]
  exact ran

theorem checked_storage_array_correct {H : HTy} (heap : Heap H) (primitive : PrimTy) (values : List primitive.Denote)
    (bounded : values.length < W) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.prim primitive))) source (primitiveArrayValue primitive values bounded)) :
    (∃ fits, CheckedStorageArrayResult heap primitive values bounded base frame cursor machine source fits) ∨
      (¬ cursor.val + (values.length + 1) < W ∧ run checkedStorageArrayCode (machine.push (.slot source)) = .revert) := by
  by_cases fits : cursor.val + (values.length + 1) < W
  · exact Or.inl ⟨fits,checked_storage_array_success heap primitive values bounded base frame cursor machine source L allocator represented fits⟩
  · right
    refine ⟨fits,?_⟩
    rw [checked_storage_array_run heap primitive values bounded base frame cursor machine source L allocator represented,if_neg fits]

def checkedStorageArray : CheckedStorageArrayCertificate := ⟨checked_storage_array_correct⟩

#print axioms storage_capacity_guard_run
#print axioms checked_storage_array_run
#print axioms checked_storage_array_success
#print axioms checked_storage_array_correct
#print axioms checkedStorageArray
end Solidity.Backend.MemoryCopies
