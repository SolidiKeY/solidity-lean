import Solidity.Backend.MemoryCopies.GuardedDefaultDeclarationInterface

/-! Prepending the existing guard to the actual selected declaration preserves
its full successful contract and makes capacity refusal explicit. Selection,
Source semantics, frame layout and the production compiler are unchanged. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem guarded_default_declaration_run {C : Contract} {Γ : Ctx} {b : Nat} {frag : Frag Γ}
    {root : RefTy} {name : Var} {defaultable : (Ty.ref root).defaultOkS = true}
    {memory : (Ty.ref root).mapFree = true} (child : SelectedCheckedDefault root memory)
    (selected : SelectedDefaultDeclaration (C := C) b frag root name defaultable memory)
    {frame : Nat} (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) :
    run (guardedDefaultDeclarationCode selected) machine =
      if cursor.val + ReferenceDefaults.defaultCells (.ref root) < W
      then run selected.compiled.code machine else .revert := by
  have guard : run (defaultCapacityGuard (ReferenceDefaults.defaultCells (.ref root))) machine =
      if cursor.val + ReferenceDefaults.defaultCells (.ref root) < W then .ok machine 0 else .revert :=
    default_capacity_guard_run _ child.builder.positive machine cursor allocator.free.cell
  rw [guardedDefaultDeclarationCode]
  by_cases fits : cursor.val + ReferenceDefaults.defaultCells (.ref root) < W
  · rw [if_pos fits] at guard
    rw [run_append_ok guard, if_pos fits]
  · rw [if_neg fits] at guard
    rw [run_append_revert guard, if_neg fits]

theorem guarded_default_declaration_checked {C : Contract} {Γ : Ctx} {b : Nat} {frag : Frag Γ}
    {root : RefTy} {name : Var} {defaultable : (Ty.ref root).defaultOkS = true}
    {memory : (Ty.ref root).mapFree = true} (child : SelectedCheckedDefault root memory)
    (selected : SelectedDefaultDeclaration (C := C) b frag root name defaultable memory)
    {frame : Nat} (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) :
    run (guardedDefaultDeclarationCode selected) machine =
      if cursor.val + liveWordCount (SVal.dflt (.ref root)) < W
      then run selected.compiled.code machine else .revert := by
  have available : (ReferenceDefaults.compileDefault root memory).isSome = true := by
    rw [child.selected]; rfl
  rw [selected_default_words root memory available]
  exact guarded_default_declaration_run child selected state base cursor machine allocator

theorem guarded_default_declaration_success {C : Contract} {Γ : Ctx} {b : Nat} {frag : Frag Γ}
    {root : RefTy} {name : Var} {defaultable : (Ty.ref root).defaultOkS = true}
    {memory : (Ty.ref root).mapFree = true} (child : SelectedCheckedDefault root memory)
    (selected : SelectedDefaultDeclaration (C := C) b frag root name defaultable memory)
    {L frame : Nat} (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (locals : b + frameNeedStmt (Stmt.declMem (C := C) (Γ := Γ) root name none defaultable memory) ≤ frame)
    (fits : cursor.val + ReferenceDefaults.defaultCells (.ref root) < W) :
    GuardedDefaultDeclarationSuccess (L := L) (frame := frame) selected state base cursor machine fits := by
  obtain ⟨base',target,execution,reached,stack,extension,growth⟩ :=
    selected.execute state base machine represented locals (.inr ⟨positive,cursor,allocator,fits⟩)
  refine ⟨base',target,?_,reached,stack,extension,growth,?_,selected_default_allocation child state.heap⟩
  · rw [guarded_default_declaration_run child selected state base cursor machine allocator, if_pos fits]
    exact execution
  · exact growth cursor positive allocator fits

theorem guarded_default_declaration_correct {C : Contract} {Γ : Ctx} {b : Nat} {frag : Frag Γ}
    {root : RefTy} {name : Var} {defaultable : (Ty.ref root).defaultOkS = true}
    {memory : (Ty.ref root).mapFree = true} (child : SelectedCheckedDefault root memory)
    (selected : SelectedDefaultDeclaration (C := C) b frag root name defaultable memory)
    {L frame : Nat} (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (locals : b + frameNeedStmt (Stmt.declMem (C := C) (Γ := Γ) root name none defaultable memory) ≤ frame) :
    (∃ fits, GuardedDefaultDeclarationSuccess (L := L) (frame := frame)
      selected state base cursor machine fits) ∨
    (¬ cursor.val + ReferenceDefaults.defaultCells (.ref root) < W ∧
      run (guardedDefaultDeclarationCode selected) machine = .revert) := by
  by_cases fits : cursor.val + ReferenceDefaults.defaultCells (.ref root) < W
  · exact .inl ⟨fits,guarded_default_declaration_success child selected state base cursor machine
      represented allocator positive locals fits⟩
  · refine .inr ⟨fits,?_⟩
    rw [guarded_default_declaration_run child selected state base cursor machine allocator, if_neg fits]

def guardedDefaultDeclaration : GuardedDefaultDeclarationCertificate :=
  ⟨guarded_default_declaration_checked,guarded_default_declaration_correct⟩

/--
info: 'Solidity.Backend.MemoryCopies.guarded_default_declaration_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms guarded_default_declaration_run
/--
info: 'Solidity.Backend.MemoryCopies.guarded_default_declaration_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms guarded_default_declaration_checked
/--
info: 'Solidity.Backend.MemoryCopies.guarded_default_declaration_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms guarded_default_declaration_success
/--
info: 'Solidity.Backend.MemoryCopies.guarded_default_declaration_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms guarded_default_declaration_correct
/--
info: 'Solidity.Backend.MemoryCopies.guardedDefaultDeclaration' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms guardedDefaultDeclaration
end Solidity.Backend.MemoryCopies
