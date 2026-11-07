import Solidity.Optimizer.Controls

/-! Equality validation has a real accepted pair and a distinct rejected pair.
No reject-all validator is used as the witness for an acceptance premise. -/
namespace H62.CompilerTransport.OptimizerFixture
open Solidity.Optimizer

def relation : Nat → Nat → Prop := Eq
def validator : Validator relation := Validator.equality Nat
def identity : Pass Nat := fun n => n
def passes : List (Pass Nat) := []
def yulIdentity : Pass (Solidity.Yul.Stmt [] [] ⟨false,false⟩ 0) := fun p => p

theorem accepted : validator.validate 37 37 = true := rfl
theorem distinct : ¬ relation 37 38 := by
  change ¬ ((37 : Nat) = 38)
  decide
theorem rejected : validator.validate 37 38 = false := rfl
theorem preserves : Preserves relation identity := fun _ => rfl
theorem reflexive : ∀ p : Nat, relation p p := fun _ => rfl
theorem transitive : ∀ {p q r : Nat}, relation p q → relation q r → relation p r :=
  fun first second => first.trans second
theorem each : ∀ pass, pass ∈ passes → Preserves relation pass := by
  intro pass member
  cases member

#print axioms accepted
#print axioms distinct
#print axioms preserves
end H62.CompilerTransport.OptimizerFixture
