import Solidity.Optimizer.Pass

/-! Composition and validator controls independent of the pending D6 instance. -/
namespace Solidity.Optimizer
universe u

/-- Identity is a left pipeline unit. -/
theorem Pass.id_comp {P : Type u} (pass : Pass P) :
    (fun p => p).comp pass = pass := rfl

/-- Identity is a right pipeline unit. -/
theorem Pass.comp_id {P : Type u} (pass : Pass P) :
    pass.comp (fun p => p) = pass := rfl

/-- Pipeline parenthesization does not change the actual output artifact. -/
theorem Pass.comp_assoc {P : Type u} (a b c : Pass P) :
    (a.comp b).comp c = a.comp (b.comp c) := rfl

/-- The conservative validator never admits an uncertified proposal. -/
def Validator.reject {P : Type u} (Related : P → P → Prop) : Validator Related where
  validate _ _ := false
  sound _ _ accepted := Bool.noConfusion accepted

/-- Equality validation is executable whenever intrinsic program equality is
already decidable; this does not install a classical decision procedure. -/
def Validator.equality (P : Type u) [DecidableEq P] : Validator (fun p q : P => p = q) where
  validate p q := decide (p = q)
  sound _ _ accepted := of_decide_eq_true accepted

/-- Rejection is observationally the original executable pass, not an error. -/
theorem validated_reject {P : Type u} (Related : P → P → Prop) (proposal : Pass P) :
    validated (Validator.reject Related) proposal = (fun p => p) := rfl

/-- An accepted proposal executes that exact proposal. -/
theorem validated_accept {P : Type u} {Related : P → P → Prop}
    (validator : Validator Related) (proposal : Pass P) (p : P)
    (accepted : validator.validate p (proposal p) = true) :
    validated validator proposal p = proposal p := by
  simp only [validated, accepted, ite_true]

/-- An observation-changing proposal cannot be accepted by a sound validator. -/
theorem Validator.rejects_unsound {P : Type u} {Related : P → P → Prop}
    (validator : Validator Related) {p q : P} (changed : ¬ Related p q) :
    validator.validate p q = false := by
  cases accepted : validator.validate p q with
  | false => rfl
  | true => exact False.elim (changed (validator.sound p q accepted))

/-- Identity proposals survive validation even when the checker rejects. -/
theorem validated_id {P : Type u} {Related : P → P → Prop}
    (validator : Validator Related) : validated validator (fun p => p) = (fun p => p) := by
  funext p
  unfold validated
  split <;> rfl

end Solidity.Optimizer
