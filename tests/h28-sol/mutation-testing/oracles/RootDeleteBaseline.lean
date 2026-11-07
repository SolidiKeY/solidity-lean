import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! An inhabited concrete instance of the production `storageRootDelete`:
the root `x` holds 7 and `delete x;` clears it. -/
namespace H28.RootDeleteBaseline
open Solidity

def xName : Name := String.singleton 'x'
def C : Contract := { vars := [(xName, .prim .uint)] }
def root : Loc C [] (.prim .uint) := .root xName rfl
def start : State C [] := (State.init C).withStorage (.cons (.prim ⟨7, rfl⟩) .nil)
def statement : Stmt C [] [] := .delete root
def intended : Premise C [] [] :=
  .update (.snoc .nil (.storage (Tms.STerm.delAt Tms.STerm.storage (Tms.PTerm.root xName rfl))))
def deleted : State C [] := (State.init C).withStorage (.cons (.prim ⟨0, rfl⟩) .nil)

/-- The production rule deletes at the root. -/
theorem source_link : Taclet C 0 .box statement intended := .storageRootDelete

/-- The concrete typed input exists, rather than an empty relation. -/
theorem input_inhabited : Nonempty (State C []) := ⟨start⟩

/-- The run, independent of the rule, clears the root. -/
theorem actual_run : statement.runR start = .ok ⟨deleted, List.prefix_refl _⟩ := by
  with_unfolding_all rfl

#print axioms source_link
#print axioms input_inhabited
#print axioms actual_run
set_option pp.fullNames true
#check @source_link
#check @actual_run
end H28.RootDeleteBaseline
