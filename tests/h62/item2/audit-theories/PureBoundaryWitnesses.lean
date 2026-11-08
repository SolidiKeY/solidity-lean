import Solidity.Theory.Mutability.Pure
import tests.h62.item2.«audit-theories».AssignableWitnesses

/-!
Eight original Pure interface input packets: three outside-state laws, result
mapping, three loop mapping interfaces and a state-independent simple value.
Loop functions commute at EVERY natural input under a nonidentity successor
map; a real iteration then terminates. Populated outside storage actually changes.
This is partial Pure coverage and does not discharge remaining Pure interfaces.
-/
namespace H62.AuditTheories
open Solidity
open Solidity.Theory.Mutability

/-- An outside differing at a real bool root. -/
def pureChangedOutside : Outside bridgeContract :=
  {outside assignableStart with
    storage := .cons (.array .nil .nil (by decide)) (.cons (.prim true) .nil)}
/-- A nonidentity mapping between loop-state spaces. -/
def pureLoopMap (n : Nat) : Nat := n + 1
/-- The original body increments. -/
def pureLoopBody (n : Nat) : TRes Nat := .ok (n + 1)
/-- Exactly one iteration from zero. -/
def pureLoopCond (n : Nat) : TRes Bool := .ok (n == 0)
/-- The mapped body increments in the successor-shifted space. -/
def pureMappedBody (n : Nat) : TRes Nat := .ok (n + 1)
/-- The mapped starting point is one. -/
def pureMappedCond (n : Nat) : TRes Bool := .ok (n == 1)

/-- The concrete outside replacement changes an observable declared word. -/
theorem pure_outside_change_visible :
    assignableStart.storage.find bridgeFlag = some (.prim false) ∧
      (withOutside assignableStart pureChangedOutside).storage.find bridgeFlag = some (.prim true) :=
  ⟨rfl, rfl⟩

/-- Entire body commutation premise, not just the selected starting point. -/
theorem pure_loop_body_commutes :
    ∀ a, pureMappedBody (pureLoopMap a) = (pureLoopBody a).map pureLoopMap := fun _ => rfl

/-- Entire condition commutation premise for the same functions. -/
theorem pure_loop_condition_commutes :
    ∀ a, pureMappedCond (pureLoopMap a) = pureLoopCond a := by
  intro a
  cases a <;> rfl

/-- Both selected loops make a real step and finish, rather than diverging. -/
theorem pure_loop_success :
    Solidity.TLoop.run pureLoopBody pureLoopCond 0 = .ok 1 ∧
      Solidity.TLoop.run pureMappedBody pureMappedCond (pureLoopMap 0) = .ok 2 :=
  ⟨Solidity.TLoop.run_of_iterN (n := 2) rfl,
    Solidity.TLoop.run_of_iterN (n := 2) rfl⟩

/-- The complete intrinsic state telescope has a populated simultaneous instance. -/
theorem pure_restore_joint_witness :
    ∃ (C : Contract) (Γ : Ctx) (σ : State C Γ), withOutside σ (outside σ) = σ :=
  ⟨bridgeContract, [], assignableStart, rfl⟩

/-- Selected state and a genuinely different outside coexist. -/
theorem pure_replace_joint_witness :
    ∃ (C : Contract) (Γ : Ctx) (σ : State C Γ) (w : Outside C),
      outside (withOutside σ w) = w :=
  ⟨bridgeContract, [], assignableStart, pureChangedOutside, rfl⟩

/-- Both outside arguments are supplied alongside the same populated state. -/
theorem pure_replace_twice_joint_witness :
    ∃ (C : Contract) (Γ : Ctx) (σ : State C Γ) (w w' : Outside C),
      withOutside (withOutside σ w) w' = withOutside σ w' :=
  ⟨bridgeContract, [], assignableStart, outside assignableStart, pureChangedOutside, rfl⟩

/-- Mapping functions and an actual successful value share one result packet. -/
theorem pure_result_map_joint_witness :
    ∃ (α β γ : Type) (f : α → β) (g : β → γ) (x : TRes α),
      (x.map f).map g = x.map (g ∘ f) ∧ ∃ v, x = .ok v :=
  ⟨Nat, Nat, Nat, (fun n => n + 1), (fun n => 2 * n), .ok 3, rfl, 3, rfl⟩

/-- Both universal mapping laws hold together with a nontrivial successful step. -/
theorem pure_loop_step_joint_witness :
    ∃ (α β : Type) (f : α → β) (body : α → TRes α) (c : α → TRes Bool)
      (body' : β → TRes β) (c' : β → TRes Bool) (a : α),
      (∀ x, body' (f x) = (body x).map f) ∧ (∀ x, c' (f x) = c x) ∧
        ∃ next, Solidity.TLoop.step body c a = .inl next :=
  ⟨Nat, Nat, pureLoopMap, pureLoopBody, pureLoopCond, pureMappedBody, pureMappedCond,
    0, pure_loop_body_commutes, pure_loop_condition_commutes, 1, rfl⟩

/-- The late iteration budget and initial state coexist with BOTH universal laws. -/
theorem pure_loop_iter_joint_witness :
    ∃ (α β : Type) (f : α → β) (body : α → TRes α) (c : α → TRes Bool)
      (body' : β → TRes β) (c' : β → TRes Bool) (n : Nat) (a : α),
      (∀ x, body' (f x) = (body x).map f) ∧ (∀ x, c' (f x) = c x) ∧
        ∃ v, Solidity.TLoop.iterN body c n a = .inr (.ok v) :=
  ⟨Nat, Nat, pureLoopMap, pureLoopBody, pureLoopCond, pureMappedBody, pureMappedCond,
    2, 0, pure_loop_body_commutes, pure_loop_condition_commutes, 1, rfl⟩

/-- A successful terminating run accompanies both global function laws. -/
theorem pure_loop_run_joint_witness :
    ∃ (α β : Type) (f : α → β) (body : α → TRes α) (c : α → TRes Bool)
      (body' : β → TRes β) (c' : β → TRes Bool) (a : α),
      (∀ x, body' (f x) = (body x).map f) ∧ (∀ x, c' (f x) = c x) ∧
        ∃ v, Solidity.TLoop.run body c a = .ok v :=
  ⟨Nat, Nat, pureLoopMap, pureLoopBody, pureLoopCond, pureMappedBody, pureMappedCond,
    0, pure_loop_body_commutes, pure_loop_condition_commutes, 1, pure_loop_success.1⟩

/-- All inherited state/outside/type data and the no-state-read premise coexist. -/
theorem pure_simple_joint_witness :
    ∃ (C : Contract) (Γ : Ctx) (σ : State C Γ) (w : Outside C) (p : PrimTy)
      (s : Simple C Γ p), (Val.simple s).readsState = false ∧
        s.evalT (withOutside σ w) = s.evalT σ :=
  ⟨bridgeContract, [], assignableStart, pureChangedOutside, .bool, .bool true, rfl, rfl⟩

#print axioms pure_outside_change_visible
#print axioms pure_loop_body_commutes
#print axioms pure_loop_condition_commutes
#print axioms pure_loop_success
#print axioms pure_restore_joint_witness
#print axioms pure_replace_joint_witness
#print axioms pure_replace_twice_joint_witness
#print axioms pure_result_map_joint_witness
#print axioms pure_loop_step_joint_witness
#print axioms pure_loop_iter_joint_witness
#print axioms pure_loop_run_joint_witness
#print axioms pure_simple_joint_witness
end H62.AuditTheories
