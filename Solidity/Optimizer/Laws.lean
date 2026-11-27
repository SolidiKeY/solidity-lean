import Solidity.Optimizer.Pass

namespace Solidity.Optimizer
universe u

theorem Pass.id_comp {P : Type u} (pass : Pass P) :
    (fun p => p).comp pass = pass := rfl

theorem Pass.comp_id {P : Type u} (pass : Pass P) :
    pass.comp (fun p => p) = pass := rfl

theorem Pass.comp_assoc {P : Type u} (a b c : Pass P) :
    (a.comp b).comp c = a.comp (b.comp c) := rfl

def Validator.reject {P : Type u} (Related : P → P → Prop) : Validator Related where
  validate _ _ := false
  sound _ _ accepted := Bool.noConfusion accepted

def Validator.equality (P : Type u) [DecidableEq P] : Validator (fun p q : P => p = q) where
  validate p q := decide (p = q)
  sound _ _ accepted := of_decide_eq_true accepted

theorem validated_reject {P : Type u} (Related : P → P → Prop) (proposal : Pass P) :
    validated (Validator.reject Related) proposal = (fun p => p) := rfl

theorem validated_accept {P : Type u} {Related : P → P → Prop}
    (validator : Validator Related) (proposal : Pass P) (p : P)
    (accepted : validator.validate p (proposal p) = true) :
    validated validator proposal p = proposal p := by
  simp only [validated, accepted, ite_true]

theorem Validator.rejects_unsound {P : Type u} {Related : P → P → Prop}
    (validator : Validator Related) {p q : P} (changed : ¬ Related p q) :
    validator.validate p q = false := by
  cases accepted : validator.validate p q with
  | false => rfl
  | true => exact False.elim (changed (validator.sound p q accepted))

theorem validated_id {P : Type u} {Related : P → P → Prop}
    (validator : Validator Related) : validated validator (fun p => p) = (fun p => p) := by
  funext p
  unfold validated
  split <;> rfl

def Pass.pipeline {P : Type u} : List (Pass P) → Pass P
  | [] => fun p => p
  | first :: rest => first.comp (Pass.pipeline rest)

theorem Pass.pipeline_append {P : Type u} (first second : List (Pass P)) :
    Pass.pipeline (first ++ second) = (Pass.pipeline first).comp (Pass.pipeline second) := by
  induction first with
  | nil => rfl
  | cons pass rest ih =>
    simp only [List.cons_append, Pass.pipeline, ih, Pass.comp_assoc]

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

def guardedPipeline {P : Type u} {Related : P → P → Prop}
    (validator : Validator Related) (proposals : List (Pass P)) : Pass P :=
  Pass.pipeline (proposals.map (validated validator))

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
