import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! An inhabited concrete instance of the production `storageRootIncrement`
at the uint256 maximum: the checked increment reverts, independently of the
rule. -/
namespace H28.RootIncBaseline
open Solidity

def xName : Name := String.singleton 'x'
def C : Contract := { vars := [(xName, .prim .uint)] }
def maximum : PrimTy.uint.Denote := ⟨Semantics.uintBound - 1, by decide +kernel⟩
def σ : State C [] := (State.init C).withStorage (.cons (.prim maximum) .nil)
def statement : Stmt C [] [] := .incDec .preInc rfl (.root xName rfl)
def intended : Premise C [] [] := .update (Upd.nil.snoc (UpdElem.storage
  (Tms.STerm.save Tms.STerm.storage (Tms.PTerm.root xName rfl)
    (Tms.SValT.val (Tms.Term.bumped .preInc rfl
      (Tms.Term.find Tms.STerm.storage (Tms.PTerm.root xName rfl)))))))

/-- The production rule writes the checked step. -/
theorem source_link : Taclet C 0 .diamond statement intended := .storageRootIncrement

/-- The concrete typed input exists, rather than an empty relation. -/
theorem input_inhabited : Nonempty (State C []) := ⟨σ⟩

/-- The real run reverts at the overflow boundary. -/
theorem overflowing_run : statement.runR σ = .error .revert := by with_unfolding_all rfl

#print axioms source_link
#print axioms input_inhabited
#print axioms overflowing_run
set_option pp.fullNames true
#check @source_link
#check @overflowing_run
end H28.RootIncBaseline
