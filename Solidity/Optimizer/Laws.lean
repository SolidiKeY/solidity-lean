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

/-- Run a finite pipeline in list order. The empty pipeline is identity. -/
def Pass.pipeline {P : Type u} : List (Pass P) → Pass P
  | [] => fun p => p
  | first :: rest => first.comp (Pass.pipeline rest)

/-- Appending pipeline descriptions composes their actual output artifacts. -/
theorem Pass.pipeline_append {P : Type u} (first second : List (Pass P)) :
    Pass.pipeline (first ++ second) = (Pass.pipeline first).comp (Pass.pipeline second) := by
  induction first with
  | nil => rfl
  | cons pass rest ih =>
    simp only [List.cons_append, Pass.pipeline, ih, Pass.comp_assoc]

/-- Every stage is certified on all of its inputs, including intermediate ones. -/
theorem Preserves.pipeline {P : Type u} {Related : P → P → Prop}
    (refl : ∀ p, Related p p)
    (trans : ∀ {p q r}, Related p q → Related q r → Related p r)
    (passes : List (Pass P))
    (each : ∀ pass, pass ∈ passes → Preserves Related pass) :
    Preserves Related (Pass.pipeline passes) := by
  induction passes with
  | nil => exact refl
  | cons first rest ih =>
    exact Preserves.comp (Related := Related) trans (each first (List.mem_cons_self))
      (ih (fun pass member => each pass (List.mem_cons_of_mem first member)))

/-- Validate each stage against its current input; rejection keeps that input. -/
def guardedPipeline {P : Type u} {Related : P → P → Prop}
    (validator : Validator Related) (proposals : List (Pass P)) : Pass P :=
  Pass.pipeline (proposals.map (validated validator))

/-- Arbitrary untrusted finite proposals become safe through stage validation. -/
theorem guardedPipeline_preserves {P : Type u} {Related : P → P → Prop}
    (refl : ∀ p, Related p p)
    (trans : ∀ {p q r}, Related p q → Related q r → Related p r)
    (validator : Validator Related) (proposals : List (Pass P)) :
    Preserves Related (guardedPipeline validator proposals) := by
  apply Preserves.pipeline refl trans
  intro pass member
  obtain ⟨proposal, _, same⟩ := List.mem_map.mp member
  subst pass
  exact validated_preserves refl validator proposal

end Solidity.Optimizer
