import Lean
namespace Solidity.Optimizer

universe u

/-- Total optimizer at a fixed intrinsic program type. -/
abbrev Pass (Prog : Type u) := Prog → Prog

/-- Every input is related to the actual output; no input-domain exclusion. -/
def Preserves {Prog : Type u} (Related : Prog → Prog → Prop) (pass : Pass Prog) : Prop :=
  ∀ p, Related p (pass p)

/-- Executable translation validation. Soundness is a proof, not an assumption
added to each accepted program's public correctness theorem. -/
structure Validator {Prog : Type u} (Related : Prog → Prog → Prop) where
  validate : Prog → Prog → Bool
  sound : ∀ p q, validate p q = true → Related p q

/-- The only trusted bridge from validator acceptance to preservation. -/
theorem validate_sound {Prog : Type u} {Related : Prog → Prog → Prop}
    (validator : Validator Related) {p q : Prog}
    (accepted : validator.validate p q = true) : Related p q :=
  validator.sound p q accepted

/-- Execute passes in pipeline order. -/
def Pass.comp {Prog : Type u} (first second : Pass Prog) : Pass Prog :=
  fun p => second (first p)

/-- Composition needs exactly transitivity of the supplied observation relation. -/
theorem Preserves.comp {Prog : Type u} {Related : Prog → Prog → Prop}
    (trans : ∀ {p q r}, Related p q → Related q r → Related p r)
    {first second : Pass Prog} (hfirst : Preserves Related first)
    (hsecond : Preserves Related second) : Preserves Related (first.comp second) :=
  fun p => trans (hfirst p) (hsecond (first p))

/-- Rejecting a proposal returns the original program. -/
def validated {Prog : Type u} {Related : Prog → Prog → Prop}
    (validator : Validator Related) (proposal : Pass Prog) : Pass Prog :=
  fun p => if validator.validate p (proposal p) then proposal p else p

/-- A sound validator makes an arbitrary proposal safe, including rejection. -/
theorem validated_preserves {Prog : Type u} {Related : Prog → Prog → Prop}
    (refl : ∀ p, Related p p) (validator : Validator Related) (proposal : Pass Prog) :
    Preserves Related (validated validator proposal) := by
  intro p
  unfold validated
  split
  next accepted => exact validator.sound p (proposal p) accepted
  next _ => exact refl p

end Solidity.Optimizer


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


/-!
# O01 framework controls

Scalar equality controls test the validator trust boundary, not EVM or D6.
Intrinsic witnesses exercise existing nonempty typed syntax. They do not claim
that an identity pass or a reject-all validator implements O02/O03.
-/
namespace Solidity.Optimizer.Controls

/-- Accepting control: the executable checker admits an equal pair. -/
theorem equal_accepted : (Validator.equality Nat).validate 37 37 = true := rfl

/-- Negative control: an unequal proposal is rejected. -/
theorem changed_rejected : (Validator.equality Nat).validate 37 38 = false := rfl

/-- The rejected untrusted proposal cannot change the executable result. -/
theorem changed_fallback : validated (Validator.equality Nat) Nat.succ 37 = 37 := rfl

/-- Soundness implies that no checker for equality can admit this mutation. -/
theorem no_sound_checker_accepts (validator : Validator (fun p q : Nat => p = q)) :
    validator.validate 37 38 = false :=
  validator.rejects_unsound (by decide)

/-- Composition with two guarded proposals remains certified for equality. -/
theorem combination (first second : Pass Nat) :
    Preserves Eq ((validated (Validator.equality Nat) first).comp
      (validated (Validator.equality Nat) second)) :=
  (validated_preserves (fun _ => rfl) (Validator.equality Nat) first).comp
    (fun a b => a.trans b)
    (validated_preserves (fun _ => rfl) (Validator.equality Nat) second)

#print axioms validate_sound
#print axioms validated_preserves
#print axioms Preserves.comp
#print axioms no_sound_checker_accepts
#print axioms combination

end Solidity.Optimizer.Controls

namespace H62.OptimizerMigration
open Solidity.Optimizer

-- Every proposal is safe for scalar equality, at every input.
example (proposal : Pass Nat) (n : Nat) :
    validated (Validator.equality Nat) proposal n = n :=
  Eq.symm (validated_preserves (fun _ => rfl) (Validator.equality Nat) proposal n)

-- Mixed accept/reject stages must use the current input and preserve order.
example : guardedPipeline (Validator.equality Nat) [Nat.succ, id, fun n => n + 2] 37 = 37 := rfl
example : Pass.pipeline [Nat.succ, fun n => n * 2] 3 = 8 := rfl
example : Pass.pipeline [fun n => n * 2, Nat.succ] 3 = 7 := rfl

-- The pipeline proof must retain transitivity; equality is the tested instance.
example (ps : List (Pass Nat)) :
    Preserves Eq (guardedPipeline (Validator.equality Nat) ps) :=
  guardedPipeline_preserves (fun _ => rfl) (fun a b => a.trans b)
    (Validator.equality Nat) ps
end H62.OptimizerMigration

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.map Prod.fst |>.filter
    (fun n => n.toString.startsWith "Solidity.Optimizer.")
  for name in names.mergeSort (fun a b => a.toString ≤ b.toString) do
    if let some info := env.find? name then
      logInfo m!"INTERFACE {name} universes={repr info.levelParams}: {repr info.type}"

#print axioms Solidity.Optimizer.guardedPipeline_preserves
#print axioms Solidity.Optimizer.Preserves.pipeline
#print axioms Solidity.Optimizer.Pass.pipeline_append
