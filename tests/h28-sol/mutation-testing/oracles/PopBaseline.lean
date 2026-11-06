import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.PopBaseline
open Solidity

def arrayName : Name := String.singleton 'a'
def C : Contract := { vars := [(arrayName, .ref (.array (.prim .uint)))] }
def path : SPath C [] (.array (.prim .uint)) := .loc (.root arrayName rfl)
def location : Loc C [] (.prim .uint) := .index (.arr .dyn) path (.simple (.lit 0 rfl))
def empty : State C [] := .init C
def populated : State C [] := empty.withStorage (.cons
  (.array (.cons (.prim ⟨7, rfl⟩) .nil) .nil (by decide +kernel)) .nil)
def σ (b : Bool) : State C [] := if b then populated else empty
def statement : Stmt C [] [] := .pop path
def update : Upd C [] [] := .snoc .nil (.storage (Tms.STerm.pop Tms.STerm.storage path.lower))
def premise : Premise C [] [] := .update update

theorem source_link : Taclet C 0 .diamond statement premise := .storagePopSave (darr := path) rfl rfl

def afterPositive : State C [] := empty.withStorage (.cons (.array .nil (.cons (.prim ⟨0, rfl⟩) .nil) (by decide +kernel)) .nil)

theorem input_inhabited : ∀ _b : Bool, Nonempty (State C []) := fun b => ⟨σ b⟩
theorem failing_run : statement.runR empty = .error .revert := by with_unfolding_all rfl
theorem positive_run : statement.runR populated = .ok ⟨afterPositive, List.prefix_refl _⟩ := by with_unfolding_all rfl

#print axioms source_link
#print axioms input_inhabited
#print axioms failing_run
#print axioms positive_run
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @failing_run
#check @positive_run
end H28.PopBaseline
