import Solidity.Backend.MemoryCopies.CheckedDefaultInterface

/-! Production selection is unchanged. A guard discharges capacity before
executing the existing builder and transports every default/allocator clause. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def selectedCheckedDefault (root : RefTy) (memory : (Ty.ref root).mapFree = true)
    (supported : (ReferenceDefaults.compileDefault root memory).isSome = true) :
    SelectedCheckedDefault root memory where
  builder := (ReferenceDefaults.compileDefault root memory).get supported
  selected := (Option.some_get supported).symm

def checkedNestedDefault (element : Ty) (dimensions : List Nat)
    (memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true) :
    SelectedCheckedDefault (nestedArrayType element dimensions) memory :=
  selectedCheckedDefault _ memory (nested_selection_total element dimensions memory)

theorem default_capacity_guard_run (cost : Nat) (positive : 0 < cost) (machine : Machine)
    (cursor : Fin W) (cell : machine.mem 0 = .val cursor) :
    run (defaultCapacityGuard cost) machine =
      if cursor.val + cost < W then .ok machine 0 else .revert := by
  by_cases bounded : cost < W
  · have threshold : W - cost < W := by omega
    by_cases fits : cursor.val + cost < W
    · have comparison : cursor.val < W - cost := by omega
      simp only [defaultCapacityGuard,assertTop,↓reduceIte,if_pos bounded,List.cons_append,List.nil_append,run,exec_cons_zero,
        Instr.step,Machine.next,Out.ok_bind,exec_nil,cell,wmod_def,Nat.mod_eq_of_lt threshold,
        comparison,decide_true,bword,Nat.succ_ne_self,exec_cons_succ,if_pos fits]
    · have comparison : ¬ cursor.val < W - cost := by omega
      simp only [defaultCapacityGuard,assertTop,↓reduceIte,Bool.false_eq_true,if_pos bounded,List.cons_append,List.nil_append,run,exec_cons_zero,
        Instr.step,Machine.next,Out.ok_bind,exec_nil,cell,wmod_def,Nat.mod_eq_of_lt threshold,
        comparison,decide_false,bword,if_neg fits,Out.revert_bind]
  · have nofit : ¬ cursor.val + cost < W := by omega
    simp only [defaultCapacityGuard,if_neg bounded,if_neg nofit,run,exec_cons_zero,Instr.step,Out.revert_bind]

theorem SelectedCheckedDefault.run_checked {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    run selected.code machine = if cursor.val + ReferenceDefaults.defaultCells (.ref root) < W
      then run selected.builder.code machine else .revert := by
  have guard : run (defaultCapacityGuard (ReferenceDefaults.defaultCells (.ref root))) machine =
      if cursor.val + ReferenceDefaults.defaultCells (.ref root) < W then .ok machine 0 else .revert :=
    default_capacity_guard_run _ selected.builder.positive machine cursor allocator.free.cell
  rw [SelectedCheckedDefault.code]
  by_cases fits : cursor.val + ReferenceDefaults.defaultCells (.ref root) < W
  · rw [if_pos fits] at guard
    rw [run_append_ok guard,if_pos fits]
  · rw [if_neg fits] at guard
    rw [run_append_revert guard,if_neg fits]

theorem SelectedCheckedDefault.success {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (fits : cursor.val + ReferenceDefaults.defaultCells (.ref root) < W) :
    Objects.DefaultBuildResult heap root memory selected.code
      (ReferenceDefaults.defaultCells (.ref root)) base frame cursor machine fits := by
  obtain ⟨base',target,ran,allocated,rootAt,extension,shape,below,gaps⟩ :=
    selected.builder.correct heap base frame cursor machine allocator fits
  refine ⟨base',target,?_,allocated,rootAt,extension,shape,below,gaps⟩
  rw [selected.run_checked heap base frame cursor machine allocator,if_pos fits]
  exact ran

theorem SelectedCheckedDefault.correct {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    (∃ fits, Objects.DefaultBuildResult heap root memory selected.code
      (ReferenceDefaults.defaultCells (.ref root)) base frame cursor machine fits) ∨
    (¬ cursor.val + ReferenceDefaults.defaultCells (.ref root) < W ∧ run selected.code machine = .revert) := by
  by_cases fits : cursor.val + ReferenceDefaults.defaultCells (.ref root) < W
  · exact Or.inl ⟨fits,selected.success heap base frame cursor machine allocator fits⟩
  · right
    refine ⟨fits,?_⟩
    rw [selected.run_checked heap base frame cursor machine allocator,if_neg fits]

def checkedDefault : CheckedDefaultCertificate := ⟨SelectedCheckedDefault.correct⟩

/--
info: 'Solidity.Backend.MemoryCopies.selectedCheckedDefault' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms selectedCheckedDefault
/--
info: 'Solidity.Backend.MemoryCopies.checkedNestedDefault' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms checkedNestedDefault
/--
info: 'Solidity.Backend.MemoryCopies.default_capacity_guard_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms default_capacity_guard_run
/--
info: 'Solidity.Backend.MemoryCopies.SelectedCheckedDefault.run_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SelectedCheckedDefault.run_checked
/--
info: 'Solidity.Backend.MemoryCopies.SelectedCheckedDefault.success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SelectedCheckedDefault.success
/--
info: 'Solidity.Backend.MemoryCopies.SelectedCheckedDefault.correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SelectedCheckedDefault.correct
/--
info: 'Solidity.Backend.MemoryCopies.checkedDefault' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms checkedDefault
end Solidity.Backend.MemoryCopies
