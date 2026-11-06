import Solidity.Backend.MemoryCopies.BudgetedFinite
import Solidity.Evm.MemoryStructDefaultExamples

/-! Actual existing plans with nonzero parent offsets, declaration binding,
retained earlier children and strict configurable-limit refusal controls. -/
namespace Solidity.Backend.MemoryCopies.BudgetedFiniteControls
open Evm Evm.Memory

private structure Input where
  C : Contract
  state : State C []
  base : Nat → Fin W
  machine : Machine
  represented : StateRepr 1 1 64 (Frag.init []) state base machine
  allocator : StructAllocatorRepr state.heap base 64 (wmod 128) machine
private def input : Input :=
  ⟨_, _, _, _, StructDefaultExamples.initial_repr.1, StructDefaultExamples.initial_repr.2⟩
private def basket : DefaultPlan (.struct "Basket") :=
  (defaultPlan? (.struct "Basket")).get (by decide +kernel)
private def person : DefaultPlan (.struct "Person") :=
  (defaultPlan? (.struct "Person")).get (by decide +kernel)
private def array : DefaultPlan (.array (.prim .uint)) := DefaultPlan.array .uint
private def observe : Evm.Out → Option (Nat × Nat × Nat)
  | .ok machine _ => match machine.stack, machine.mem 0, machine.mem 63 with
    | .val root :: _, .val cursor, .val old => some (root.val, cursor.val, old.val)
    | _, _, _ => none
  | _ => none
private def reached : Evm.Out → Option Machine
  | .ok machine _ => some machine
  | _ => none
private def binding : Evm.Out → Option (Nat × Nat × List Word)
  | .ok machine _ => match machine.mem 1, machine.mem 0 with
    | .val root, .val cursor => some (root.val, cursor.val, machine.stack)
    | _, _ => none
  | _ => none
private def sourceObserve {R : RefTy}
    (result : TRes (Solidity.Out input.C input.state.H [.mem R])) : Option (Nat × Nat × Nat) := do
  let out ← result.toOption
  let reference ← TEnv.get .here out.st.env
  pure (reference.id, heapWords out.st.heap, out.st.H.length)

theorem certificate_inhabited : BudgetedFiniteCertificate := budgetedFinite

theorem root_offsets : basket.root = 1 ∧ basket.cost = 2 ∧ person.root = 3 ∧ person.cost = 5 := by
  decide +kernel

theorem body_observations :
    observe (run (budgetedFiniteCode ⟨131,by decide⟩ basket []) input.machine) = some (129, 130, 99) ∧
    observe (run (budgetedFiniteCode ⟨134,by decide⟩ person []) input.machine) = some (131, 133, 99) ∧
    observe (run (budgetedFiniteCode ⟨130,by decide⟩ array []) input.machine) = some (128, 129, 99) := by
  decide +kernel

theorem declaration_observations :
    binding (run (budgetedFiniteCode ⟨131,by decide⟩ basket [.mstore (cell 1)]) input.machine) = some (129, 130, [w[77]]) ∧
    binding (run (budgetedFiniteCode ⟨134,by decide⟩ person [.mstore (cell 1)]) input.machine) = some (131, 133, [w[77]]) := by
  decide +kernel

theorem source_declarations :
    sourceObserve (TRun.declMem (.struct "Basket") none rfl input.state) = some (1, 2, 2) ∧
    sourceObserve (TRun.declMem (.struct "Person") none rfl input.state) = some (2, 5, 3) := by
  decide +kernel

theorem actual_body_contract :
    ∃ fits, BudgetedFiniteSuccess (L := 1) (b := 1) (frame := 64) (F := Frag.init [])
      ⟨134,by decide⟩ person input.state input.base (wmod 128) input.machine rfl fits :=
  ⟨by decide, budgeted_finite_success _ person input.state input.base (wmod 128) input.machine rfl
    input.represented input.allocator (by decide) (by decide)⟩

theorem actual_declaration_contract :
    GrowingResult 1 1 64 person.cost ((Frag.init []).push (.mem (.struct "Person")) .ok)
      input.state input.base input.machine (TRun.declMem (.struct "Person") none rfl input.state)
      (run (budgetedFiniteCode ⟨134,by decide⟩ person [.mstore (cell 1)]) input.machine) := by
  rcases budgeted_finite_declaration ⟨134,by decide⟩ person input.state input.base
    (wmod 128) input.machine rfl input.represented input.allocator (by decide) (by decide) with valid | ⟨refused,_⟩
  · exact valid
  · exact (refused (by decide)).elim

/-- Actual represented success and the very same run's child header, parent
pointer, cursor, reserved payload and preserved stack. -/
theorem actual_child_layout :
    ∃ fits, BudgetedFiniteSuccess (L := 1) (b := 1) (frame := 64) (F := Frag.init [])
      ⟨131,by decide⟩ basket input.state input.base (wmod 128) input.machine rfl fits ∧
      (do let after ← reached (run (budgetedFiniteCode ⟨131,by decide⟩ basket []) input.machine)
          pure (after.mem 128,after.mem 129,after.mem 0,after.mem 63,after.stack)) =
        some (w[0],w[128],w[130],w[99],[w[129],w[77]]) := by
  refine ⟨by decide,budgeted_finite_success _ basket input.state input.base (wmod 128)
    input.machine rfl input.represented input.allocator (by decide) (by decide),?_⟩
  decide +kernel

theorem old_children_retained :
    (do let first ← reached (run (budgetedFiniteCode ⟨131,by decide⟩ basket []) input.machine)
        let second ← reached (run (budgetedFiniteCode ⟨136,by decide⟩ person []) first)
        pure (second.mem 128,second.mem 129,second.mem 0,second.stack)) =
      some (w[0],w[128],w[135],[w[133],w[129],w[77]]) := by decide +kernel

theorem strict_refusals :
    run (budgetedFiniteCode ⟨130,by decide⟩ basket []) input.machine = .revert ∧
    run (budgetedFiniteCode ⟨133,by decide⟩ person [.mstore (cell 1)]) input.machine = .revert := by
  constructor <;> rw [budgeted_finite_run _ _ _ input.machine (wmod 128)
    input.allocator.arrays.free.cell,if_neg (by decide)]

theorem zero_budget_refusal :
    run (budgetedFiniteCode ⟨0,by decide⟩ array []) input.machine = .revert := by
  rw [budgeted_finite_run _ _ _ input.machine (wmod 128) input.allocator.arrays.free.cell,if_neg (by decide)]

theorem wrong_parent_rejected :
    observe (run (budgetedFiniteCode ⟨131,by decide⟩ basket []) input.machine) ≠ some (128,130,99) := by
  rw [body_observations.1]
  decide

theorem full_budget_code {R : RefTy} (plan : DefaultPlan R) (suffix : List Instr) :
    budgetedFiniteCode ⟨W,Nat.lt_succ_self W⟩ plan suffix = checkedFiniteDefaultCode plan suffix := by
  simp only [budgetedFiniteCode,budgetDefaultGuard,Nat.sub_self,Nat.zero_add,checkedFiniteDefaultCode]

/--
info: 'Solidity.Backend.MemoryCopies.BudgetedFiniteControls.certificate_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms certificate_inhabited
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedFiniteControls.root_offsets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms root_offsets
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedFiniteControls.body_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms body_observations
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedFiniteControls.declaration_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms declaration_observations
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedFiniteControls.source_declarations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms source_declarations
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedFiniteControls.actual_body_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_body_contract
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedFiniteControls.actual_declaration_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_declaration_contract
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedFiniteControls.actual_child_layout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_child_layout
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedFiniteControls.old_children_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms old_children_retained
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedFiniteControls.strict_refusals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms strict_refusals
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedFiniteControls.zero_budget_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms zero_budget_refusal
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedFiniteControls.wrong_parent_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms wrong_parent_rejected
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedFiniteControls.full_budget_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms full_budget_code
end Solidity.Backend.MemoryCopies.BudgetedFiniteControls
