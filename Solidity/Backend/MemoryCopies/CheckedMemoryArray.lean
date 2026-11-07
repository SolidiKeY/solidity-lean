import Solidity.Backend.MemoryCopies.CheckedMemoryArrayInterface

/-! The actual free-pointer/length guard discharges capacity before the existing
fresh copy. Insufficient capacity is explicit word-target revert only. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem capacity_remaining (cursor : Fin W) :
    (W - 1 + (W - cursor.val)) % W = W - 1 - cursor.val := by
  have positive : 0 < W := W_pos
  have bounded : cursor.val < W := cursor.isLt
  have equation : W - 1 + (W - cursor.val) = W + (W - 1 - cursor.val) := by omega
  have room : W - 1 - cursor.val < W := by omega
  simp only [equation,Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_eq_of_lt room]

theorem memory_capacity_guard_run (machine : Machine) (source cursor size : Fin W)
    (cell : machine.mem 0 = .val cursor) (header : machine.mem source.val = .val size) :
    run memoryArrayCapacityGuard (machine.push (.val source)) =
      if cursor.val + (size.val + 1) < W then .ok (machine.push (.val source)) 0 else .revert := by
  have largest : W - 1 < W := by have positive : 0 < W := W_pos; omega
  have remaining : (W - 1 + (W - cursor.val)) % W = W - 1 - cursor.val := capacity_remaining cursor
  have bounded : cursor.val < W := cursor.isLt
  by_cases fits : cursor.val + (size.val + 1) < W
  · have comparison : size.val < W - 1 - cursor.val := by omega
    simp only [memoryArrayCapacityGuard,assertTop,List.cons_append,List.nil_append,run,exec_cons_zero,
      Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,Nat.reduceSub,List.getElem?_cons_zero,
      cell,header,wmod_def,Nat.mod_eq_of_lt largest,remaining,comparison,decide_true,
      bword,↓reduceIte,
      Nat.succ_ne_self,exec_cons_succ,if_pos fits]
  · have comparison : ¬ size.val < W - 1 - cursor.val := by omega
    simp only [memoryArrayCapacityGuard,assertTop,List.cons_append,List.nil_append,run,exec_cons_zero,
      Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,Nat.reduceSub,List.getElem?_cons_zero,
      cell,header,wmod_def,Nat.mod_eq_of_lt largest,remaining,comparison,decide_false,
      bword,Bool.false_eq_true,↓reduceIte,
      if_neg fits,Out.revert_bind]

theorem checked_memory_array_run {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (input : HRef H (.array (.prim primitive))) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    run checkedMemoryArrayCode (machine.push (.val (base input.id))) =
      if cursor.val + (heap.len input .dyn + 1) < W
      then run runtimeMemoryArrayCode (machine.push (.val (base input.id))) else .revert := by
  have header : machine.mem (base input.id).val = .val ⟨heap.len input .dyn,heap.len_dyn_lt input⟩ := by
    rw [(allocator.heap.arrays .dyn input).length rfl,wmod_of_lt (heap.len_dyn_lt input)]
  have guard : run memoryArrayCapacityGuard (machine.push (.val (base input.id))) =
      if cursor.val + (heap.len input .dyn + 1) < W then .ok (machine.push (.val (base input.id))) 0 else .revert :=
    memory_capacity_guard_run machine (base input.id) cursor ⟨heap.len input .dyn,heap.len_dyn_lt input⟩ allocator.free.cell header
  rw [checkedMemoryArrayCode]
  by_cases fits : cursor.val + (heap.len input .dyn + 1) < W
  · rw [if_pos fits] at guard
    rw [run_append_ok guard,if_pos fits]
  · rw [if_neg fits] at guard
    rw [run_append_revert guard,if_neg fits]

theorem checked_memory_array_success {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (input : HRef H (.array (.prim primitive))) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (fits : cursor.val + (heap.len input .dyn + 1) < W) :
    CheckedMemoryArrayResult heap primitive input base frame cursor machine fits := by
  obtain ⟨base',target,ran,allocated,root,extension,shape,below,gaps,keeps,fresh⟩ :=
    runtime_memory_array_success heap primitive input base frame cursor machine allocator fits
  refine ⟨base',target,?_,allocated,root,extension,shape,below,gaps,keeps,fresh⟩
  rw [checked_memory_array_run heap primitive input base frame cursor machine allocator,if_pos fits]
  exact ran

theorem checked_memory_array_correct {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (input : HRef H (.array (.prim primitive))) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    (∃ fits, CheckedMemoryArrayResult heap primitive input base frame cursor machine fits) ∨
      (¬ cursor.val + (heap.len input .dyn + 1) < W ∧
        run checkedMemoryArrayCode (machine.push (.val (base input.id))) = .revert) := by
  by_cases fits : cursor.val + (heap.len input .dyn + 1) < W
  · exact Or.inl ⟨fits,checked_memory_array_success heap primitive input base frame cursor machine allocator fits⟩
  · right
    refine ⟨fits,?_⟩
    rw [checked_memory_array_run heap primitive input base frame cursor machine allocator,if_neg fits]

def checkedMemoryArray : CheckedMemoryArrayCertificate := ⟨checked_memory_array_correct⟩

#print axioms capacity_remaining
#print axioms memory_capacity_guard_run
#print axioms checked_memory_array_run
#print axioms checked_memory_array_success
#print axioms checked_memory_array_correct
#print axioms checkedMemoryArray
end Solidity.Backend.MemoryCopies
