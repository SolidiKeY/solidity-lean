import Solidity.Optimizer.Laws
import Solidity.Semantics.Run

/-!
# O01 interpreter-backed framework controls

These use existing intrinsic lowering values and the actual assert Panic run.
The validator compares one supplied typed state's value results. It is not a
whole-program/D6 validator, an O02 implementation or a gas/cost claim.
-/
namespace Solidity.Optimizer.ValueValidatorControls
variable {C : Contract} {Γ : Ctx}

/-- Constructive local equality for the existing result type; no classical oracle. -/
private instance resultDecEq : DecidableEq (TRes PrimTy.uint.Denote) := fun a b => by
  cases a with
  | error x =>
    cases b with
    | error y =>
      exact if h : x = y then .isTrue (h ▸ rfl)
        else .isFalse (fun equal => h (Except.error.inj equal))
    | ok _ => exact .isFalse (fun equal => by cases equal)
  | ok x =>
    cases b with
    | error _ => exact .isFalse (fun equal => by cases equal)
    | ok y =>
      exact if h : x = y then .isTrue (h ▸ rfl)
        else .isFalse (fun equal => h (Except.ok.inj equal))

/-- Nontrivial existing typed arithmetic syntax; no replacement IR. -/
def addition : Val C Γ .uint :=
  .binop .add rfl rfl (.simple (.lit 2 (by decide))) (.simple (.lit 3 (by decide)))

def five : Val C Γ .uint := .simple (.lit 5 (by decide))
def four : Val C Γ .uint := .simple (.lit 4 (by decide))

/-- Exact existing evaluator result at an explicit state, including halt tags.
This per-state test relation is deliberately not the missing D6 contract. -/
def SameResultAt (state : State C Γ) (a b : Val C Γ .uint) : Prop :=
  a.evalT state = b.evalT state

/-- A computable checker whose soundness is about that exact supplied state. -/
def validatorAt (state : State C Γ) : Validator (SameResultAt state) where
  validate a b := decide (a.evalT state = b.evalT state)
  sound a b accepted := show a.evalT state = b.evalT state from of_decide_eq_true accepted

/-- Any guarded expression proposal preserves the exact supplied-state result.
The state parameter remains explicit; this is not universal D6 certification. -/
theorem checked_proposal_preserves_at (state : State C Γ)
    (proposal : Pass (Val C Γ .uint)) :
    Preserves (SameResultAt state) (validated (validatorAt state) proposal) :=
  validated_preserves (Related := SameResultAt state) (fun _ => rfl) (validatorAt state) proposal

/-- Real evaluator-result equality instantiates the generic composition law. -/
theorem sequential_preserves_at (state : State C Γ)
    (first second : Pass (Val C Γ .uint)) :
    Preserves (SameResultAt state) ((validated (validatorAt state) first).comp
      (validated (validatorAt state) second)) :=
  Preserves.comp (Related := SameResultAt state)
    (fun left right => Eq.trans left right)
    (checked_proposal_preserves_at state first) (checked_proposal_preserves_at state second)

/-- Actual typed evaluation, universally quantified over the supplied state. -/
theorem addition_result (state : State C Γ) :
    addition.evalT state = .ok (uintOfNat 5) := rfl

/-- A real value computation can be accepted against its constant result. -/
theorem correct_value_accepted (state : State C Γ) :
    (validatorAt state).validate addition five = true := rfl

/-- A wrong constant cannot pass this executable checker. -/
theorem changed_value_rejected (state : State C Γ) :
    (validatorAt state).validate addition four = false := rfl

/-- The framework fallback retains the actual original typed expression. -/
theorem changed_proposal_fallback (state : State C Γ) :
    validated (validatorAt state) (fun _ => four) addition = addition := rfl

/-- Instantiated, inhabited state and nontrivial expression in the existing IR. -/
theorem inhabited : ∃ state : State StandardExample [],
    addition.evalT state = .ok (uintOfNat 5) ∧
      (validatorAt state).validate addition four = false :=
  ⟨State.init StandardExample, rfl, rfl⟩

/-- An actual lowering program that reaches the interpreter's Panic constructor. -/
def panicProgram : Prog C Γ Γ :=
  .cons (.assert (.simple (.bool false))) .nil

/-- This is the actual program run, not a fabricated result token. -/
theorem panic_run (state : State C Γ) :
    panicProgram.run state = .error .panic := rfl

/-- Erasing that program to skip changes the observed interpreter outcome. -/
theorem panic_not_skip (state : State C Γ) :
    panicProgram.run state ≠ (Prog.nil : Prog C Γ Γ).run state := by
  intro impossible
  cases impossible

/-- Generic equality validation cannot identify Panic with a successful value. -/
theorem panic_not_value :
    (Validator.equality (TRes PrimTy.uint.Denote)).validate
      (.error .panic) (.ok (uintOfNat 0)) = false := rfl

/-- Two inhabited states of the SAME intrinsic local context. -/
def localState (value : Nat) : State StandardExample [.val .uint] :=
  (State.init StandardExample).push (t := .val .uint) (uintOfNat value)

def localRead : Val StandardExample [.val .uint] .uint := .simple (.local .here)
def localZero : Val StandardExample [.val .uint] .uint := .simple (.lit 0 (by decide))
def replaceLocal : Pass (Val StandardExample [.val .uint] .uint) := fun _ => localZero

theorem local_zero_accepted :
    (validatorAt (localState 0)).validate localRead localZero = true := rfl

theorem local_zero_output :
    validated (validatorAt (localState 0)) replaceLocal localRead = localZero := rfl

theorem local_one_rejected :
    (validatorAt (localState 1)).validate localRead localZero = false := rfl

theorem local_one_fallback :
    validated (validatorAt (localState 1)) replaceLocal localRead = localRead := rfl

theorem local_one_changed : ¬ SameResultAt (localState 1) localRead localZero := by
  change ¬ ((Except.ok (uintOfNat 1) : TRes PrimTy.uint.Denote) = .ok (uintOfNat 0))
  decide +kernel

/-- Fixing the checker at state0 produces an artifact that changes state1. -/
theorem frozen_zero_not_one : ¬ SameResultAt (localState 1) localRead
    (validated (validatorAt (localState 0)) replaceLocal localRead) :=
  local_one_changed

/-- A supplied-state certificate cannot be generalized to all environments. -/
theorem frozen_zero_not_universal :
    ¬ Preserves (fun a b : Val StandardExample [.val .uint] .uint =>
      ∀ state : State StandardExample [.val .uint], SameResultAt state a b)
      (validated (validatorAt (localState 0)) replaceLocal) := by
  intro universal
  exact frozen_zero_not_one (universal localRead (localState 1))

#print axioms local_zero_accepted
#print axioms local_zero_output
#print axioms local_one_rejected
#print axioms local_one_fallback
#print axioms local_one_changed
#print axioms frozen_zero_not_one
#print axioms frozen_zero_not_universal

#print axioms resultDecEq
#print axioms validatorAt
#print axioms checked_proposal_preserves_at
#print axioms sequential_preserves_at
#print axioms addition_result
#print axioms correct_value_accepted
#print axioms changed_value_rejected
#print axioms changed_proposal_fallback
#print axioms inhabited
#print axioms panic_run
#print axioms panic_not_skip
#print axioms panic_not_value

end Solidity.Optimizer.ValueValidatorControls
