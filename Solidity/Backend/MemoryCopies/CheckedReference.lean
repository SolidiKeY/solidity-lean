import Solidity.Backend.MemoryCopies.CheckedReferenceInterface

/-! Division bounds full demand without multiplying words. Production child
selection and existing reference-array simulation remain unchanged. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem reference_capacity_remaining (cursor : Fin W) (room : cursor.val + 1 < W) :
    (W - 2 + (W - cursor.val)) % W = W - 2 - cursor.val := by
  have large : 2 ≤ W := by decide
  have equation : W - 2 + (W - cursor.val) = W + (W - 2 - cursor.val) := by omega
  have bounded : W - 2 - cursor.val < W := by omega
  simp only [equation,Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_eq_of_lt bounded]

theorem reference_capacity_iff (childCost : Nat) (cursor size : Fin W) (room : cursor.val + 1 < W) :
    size.val ≤ (W - 2 - cursor.val) / (childCost + 1) ↔
      cursor.val + (size.val + 1 + size.val * childCost) < W := by
  rw [Nat.le_div_iff_mul_le (by omega : 0 < childCost + 1)]
  simp only [Nat.mul_add,Nat.mul_one]
  have large : 2 ≤ W := by decide
  omega

theorem reference_capacity_large (childCost : Nat) (cursor size : Fin W) (room : cursor.val + 1 < W)
    (large : W ≤ childCost + 1) :
    cursor.val + (size.val + 1 + size.val * childCost) < W ↔ size.val = 0 := by
  constructor
  · intro fits
    by_cases zero : size.val = 0
    · exact zero
    have one : 1 ≤ size.val := by omega
    have product : 1 * (childCost + 1) ≤ size.val * (childCost + 1) := Nat.mul_le_mul_right _ one
    simp only [Nat.one_mul,Nat.mul_add,Nat.mul_one] at product
    omega
  · intro zero
    rw [zero,Nat.zero_add,Nat.zero_mul,Nat.add_zero]
    exact room

theorem reference_capacity_tail_run (childCost : Nat) (machine : Machine) (cursor size : Fin W)
    (cell : machine.mem 0 = .val cursor) (room : cursor.val + 1 < W) :
    run (referenceCapacityTail childCost) (machine.push (.val size)) =
      if cursor.val + (size.val + 1 + size.val * childCost) < W
      then .ok (machine.push (.val size)) 0 else .revert := by
  by_cases bounded : childCost + 1 < W
  · have largest : W - 2 < W := by
      have large : 2 ≤ W := by decide
      omega
    have remainder : (W - 2 + (W - cursor.val)) % W = W - 2 - cursor.val := reference_capacity_remaining cursor room
    have nonzero : childCost + 1 ≠ 0 := by omega
    by_cases fits : cursor.val + (size.val + 1 + size.val * childCost) < W
    · have comparison : ¬ (W - 2 - cursor.val) / (childCost + 1) < size.val := by
        have limit : size.val ≤ (W - 2 - cursor.val) / (childCost + 1) := (reference_capacity_iff childCost cursor size room).mpr fits
        omega
      simp only [referenceCapacityTail,if_pos bounded,assertTop,List.cons_append,List.nil_append,run,exec_cons_zero,
        Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,Nat.reduceSub,List.getElem?_cons_zero,
        List.set_cons_zero,cell,wmod_def,Nat.mod_eq_of_lt largest,Nat.mod_eq_of_lt bounded,remainder,
        nonzero,comparison,decide_false,decide_true,bword,
        Bool.false_eq_true,↓reduceIte,Nat.succ_ne_self,exec_cons_succ,if_pos fits]
    · have comparison : (W - 2 - cursor.val) / (childCost + 1) < size.val := by
        have limit : ¬ size.val ≤ (W - 2 - cursor.val) / (childCost + 1) :=
          fun accepted => fits ((reference_capacity_iff childCost cursor size room).mp accepted)
        omega
      simp only [referenceCapacityTail,if_pos bounded,assertTop,List.cons_append,List.nil_append,run,exec_cons_zero,
        Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,Nat.reduceSub,List.getElem?_cons_zero,
        List.set_cons_zero,cell,wmod_def,Nat.mod_eq_of_lt largest,Nat.mod_eq_of_lt bounded,remainder,
        nonzero,comparison,decide_false,decide_true,bword,
        Bool.false_eq_true,↓reduceIte,Nat.succ_ne_self,if_neg fits,Out.revert_bind]
  · have equivalence : cursor.val + (size.val + 1 + size.val * childCost) < W ↔ size.val = 0 :=
      reference_capacity_large childCost cursor size room (by omega)
    by_cases zero : size.val = 0
    · have fits : cursor.val + (size.val + 1 + size.val * childCost) < W := equivalence.mpr zero
      rw [if_pos fits]
      simp only [referenceCapacityTail,if_neg bounded,assertTop,List.cons_append,List.nil_append,run,exec_cons_zero,
        Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,Nat.reduceSub,List.getElem?_cons_zero,
        zero,decide_true,bword,↓reduceIte,Nat.succ_ne_self,exec_cons_succ]
    · have fits : ¬ cursor.val + (size.val + 1 + size.val * childCost) < W := fun accepted => zero (equivalence.mp accepted)
      simp only [referenceCapacityTail,if_neg bounded,assertTop,List.cons_append,List.nil_append,run,exec_cons_zero,
        Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,Nat.reduceSub,List.getElem?_cons_zero,
        zero,decide_false,bword,Bool.false_eq_true,↓reduceIte,if_neg fits,Out.revert_bind]

theorem reference_capacity_guard_run (childCost : Nat) (machine : Machine) (cursor size : Fin W)
    (cell : machine.mem 0 = .val cursor) :
    run (referenceCapacityGuard childCost) (machine.push (.val size)) =
      if cursor.val + (size.val + 1 + size.val * childCost) < W
      then .ok (machine.push (.val size)) 0 else .revert := by
  have first : run (defaultCapacityGuard 1) (machine.push (.val size)) =
      if cursor.val + 1 < W then .ok (machine.push (.val size)) 0 else .revert :=
    default_capacity_guard_run 1 (by decide) (machine.push (.val size)) cursor cell
  rw [referenceCapacityGuard]
  by_cases room : cursor.val + 1 < W
  · rw [if_pos room] at first
    rw [run_append_ok first]
    exact reference_capacity_tail_run childCost machine cursor size cell room
  · rw [if_neg room] at first
    rw [run_append_revert first,if_neg (by omega)]

theorem checked_reference_run {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H) (size : Fin W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    run (checkedReferenceCode selected) (machine.push (.val size)) =
      if cursor.val + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)) < W
      then run (Objects.referenceArrayCode selected.builder.code) (machine.push (.val size)) else .revert := by
  have guard : run (referenceCapacityGuard (ReferenceDefaults.defaultCells (.ref root))) (machine.push (.val size)) =
      if cursor.val + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)) < W
      then .ok (machine.push (.val size)) 0 else .revert :=
    reference_capacity_guard_run _ machine cursor size allocator.free.cell
  rw [checkedReferenceCode]
  by_cases fits : cursor.val + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)) < W
  · rw [if_pos fits] at guard
    rw [run_append_ok guard,if_pos fits]
  · rw [if_neg fits] at guard
    rw [run_append_revert guard,if_neg fits]

theorem checked_reference_success {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H) (size : Fin W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (fits : cursor.val + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)) < W) :
    CheckedReferenceResult selected heap size base frame cursor machine fits := by
  obtain ⟨base',target,ran,allocated,rootAt,extension,shape,below,gaps⟩ :=
    Objects.referenceArray_correct selected.builder heap size base frame machine cursor allocator fits
  refine ⟨base',target,?_,allocated,rootAt,extension,shape,below,gaps⟩
  rw [checked_reference_run selected heap size base frame cursor machine allocator,if_pos fits]
  exact ran

theorem checked_reference_correct {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H) (size : Fin W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    (∃ fits, CheckedReferenceResult selected heap size base frame cursor machine fits) ∨
    (¬ cursor.val + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)) < W ∧
      run (checkedReferenceCode selected) (machine.push (.val size)) = .revert) := by
  by_cases fits : cursor.val + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)) < W
  · exact Or.inl ⟨fits,checked_reference_success selected heap size base frame cursor machine allocator fits⟩
  · right
    refine ⟨fits,?_⟩
    rw [checked_reference_run selected heap size base frame cursor machine allocator,if_neg fits]

def checkedReference : CheckedReferenceCertificate := ⟨checked_reference_correct⟩

#print axioms reference_capacity_remaining
#print axioms reference_capacity_iff
#print axioms reference_capacity_large
#print axioms reference_capacity_tail_run
#print axioms reference_capacity_guard_run
#print axioms checked_reference_run
#print axioms checked_reference_success
#print axioms checked_reference_correct
#print axioms checkedReference
end Solidity.Backend.MemoryCopies
