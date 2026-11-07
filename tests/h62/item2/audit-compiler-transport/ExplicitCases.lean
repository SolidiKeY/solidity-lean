import tests.h62.item2.«audit-compiler-transport».JointHypotheses
import Solidity.Optimizer.Laws

/-! Uniform-universe nonempty optimizer models. These are framework equality
witnesses, not Solidity bytecode or D6 adequacy proofs. -/
namespace H62.CompilerTransport.ExplicitCases
open Solidity.Optimizer
universe u

abbrev Carrier : Type u := ULift.{u} Nat
def relation : Carrier.{u} → Carrier.{u} → Prop := Eq
def identity : Pass Carrier.{u} := fun value => value
def validator : Validator relation.{u} := Validator.equality Carrier

def input37 : Carrier.{u} := ⟨37⟩
def input38 : Carrier.{u} := ⟨38⟩
theorem accepted : validator.validate input37.{u} input37 = true := rfl
theorem rejected : validator.validate input37.{u} input38 = false := rfl
theorem distinct : ¬ relation input37.{u} input38 := by
  intro same
  have bad : (37 : Nat) = 38 := congrArg ULift.down same
  cases bad

theorem preserves : Preserves relation.{u} identity := fun _ => rfl
theorem reflexive : ∀ p : Carrier.{u}, relation p p := fun _ => rfl
theorem transitive : ∀ {p q r : Carrier.{u}}, relation p q → relation q r → relation p r :=
  fun first second => first.trans second

def nonemptyPasses : List (Pass Carrier.{u}) := [identity]
theorem nonempty_each : ∀ pass, pass ∈ nonemptyPasses.{u} → Preserves relation pass := by
  intro pass member
  simp only [nonemptyPasses,List.mem_singleton] at member
  subst pass
  exact preserves

theorem passes_nonempty : nonemptyPasses.{u} ≠ [] := by
  intro same
  cases same

theorem pipeline_joint_nonempty :
    jointHypothesesStr% "Solidity.Optimizer.Preserves.pipeline" :=
  ⟨Carrier,relation,reflexive,@transitive,nonemptyPasses,nonempty_each,True.intro⟩

def change : Pass Carrier.{u} := fun value => ⟨value.down + 1⟩
def changingProposals : List (Pass Carrier.{u}) := [change]
theorem proposals_nonempty : changingProposals.{u} ≠ [] := by
  intro same
  cases same

theorem guarded_pipeline_joint_nonempty :
    jointHypothesesStr% "Solidity.Optimizer.guardedPipeline_preserves" :=
  ⟨Carrier,relation,reflexive,@transitive,validator,changingProposals,True.intro⟩

#print axioms pipeline_joint_nonempty
#print axioms guarded_pipeline_joint_nonempty
end H62.CompilerTransport.ExplicitCases
