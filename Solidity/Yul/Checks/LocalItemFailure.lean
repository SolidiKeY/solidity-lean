import Solidity.Yul.LocalItemFailure
import Solidity.Yul.Checks.LocalBoolFailure

namespace Solidity.Yul.Checks.LocalItemFailure

def booleanWitness : Nonempty (LocalBoolItems.Supported Solidity.Yul.Checks.LocalBoolItems.Fixture.env [] false ⟨false,false⟩ Solidity.Yul.Checks.LocalBoolItems.rawProgram) := ⟨Solidity.Yul.Checks.LocalBoolItems.rawProof⟩
def defaultWitness := Solidity.Yul.Checks.LocalDefaultItems.witness

def booleanConcrete (fuel : Nat) (state : LocalState Solidity.Yul.Checks.LocalBoolItems.Fixture.env Solidity.Yul.Checks.LocalBoolItems.Fixture.ctx.tys)
 (reached : Solidity.Source.RCtx) (halt : Solidity.Source.Halt) (next : LocalState Solidity.Yul.Checks.LocalBoolItems.Fixture.env reached) :=
 Solidity.Yul.LocalItemFailure.booleanItems Solidity.Yul.Checks.LocalBoolItems.Fixture.env [] false ⟨false,false⟩ Solidity.Yul.Checks.LocalBoolItems.Fixture.ctx.tys Solidity.Yul.Checks.LocalBoolItems.C2 Solidity.Yul.Checks.LocalBoolItems.rawProgram Solidity.Yul.Checks.LocalBoolItems.rawProof fuel state reached halt next

def defaultConcrete (fuel : Nat) (state : LocalState Solidity.Yul.Checks.LocalDefaultItems.Fixture.env Solidity.Yul.Checks.LocalDefaultItems.Fixture.ctx.tys)
 (reached : Solidity.Source.RCtx) (halt : Solidity.Source.Halt) (next : LocalState Solidity.Yul.Checks.LocalDefaultItems.Fixture.env reached) :=
 Solidity.Yul.LocalItemFailure.defaultItems Solidity.Yul.Checks.LocalDefaultItems.Fixture.env [] false ⟨false,false⟩ Solidity.Yul.Checks.LocalDefaultItems.Fixture.ctx.tys _ Solidity.Yul.Checks.LocalDefaultItems.items Solidity.Yul.Checks.LocalDefaultItems.proof fuel state reached halt next

theorem statementPartialWrite : Solidity.Yul.LocalExprStatement.discard (Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalDefaultPostIter.postFault) 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial = (.error .timeout,Solidity.Yul.Checks.LocalDefaultPostIter.assigned true) := by
  rfl

theorem initializerPartialWrite : Solidity.Yul.LocalBoolInitialization.run Solidity.Yul.Checks.LocalDefaultPostIter.postFault 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .halted .timeout (Solidity.Yul.Checks.LocalDefaultPostIter.assigned true) := by
  rfl

theorem grownBooleanTimeout : Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItems.rawProof 3 Solidity.Yul.Checks.LocalBoolItems.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolItems.rawOne := by
  rfl

theorem grownDefaultTimeout : Solidity.Yul.LocalDefaultItems.run Solidity.Yul.Checks.LocalDefaultItems.proof 6 Solidity.Yul.Checks.LocalDefaultItems.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultItems.bodyState := by
  rfl

theorem normalCompletion : Solidity.Yul.LocalDefaultItems.run Solidity.Yul.Checks.LocalDefaultItems.proof 7 Solidity.Yul.Checks.LocalDefaultItems.initial = .normal Solidity.Yul.Checks.LocalDefaultItems.finalState := by
  rfl

theorem notRevert : Solidity.Yul.LocalDefaultItems.run Solidity.Yul.Checks.LocalDefaultItems.proof 6 Solidity.Yul.Checks.LocalDefaultItems.initial ≠ .halted (.revert []) Solidity.Yul.Checks.LocalDefaultItems.bodyState := by
  intro bad; cases bad

theorem unsupportedReturn : ¬ Nonempty (Solidity.Yul.LocalBoolItems.Supported Solidity.Yul.Checks.LocalBoolItems.Fixture.env [] false ⟨false,false⟩ (Solidity.Source.RItems.stmt (Solidity.Source.RStmt.ret rfl) (Solidity.Source.RItems.nil (Γ := Solidity.Yul.Checks.LocalBoolItems.Fixture.ctx.tys)))) := by
  rintro ⟨proof⟩; cases proof

#print axioms Solidity.Yul.LocalItemFailure.statement
#print axioms Solidity.Yul.LocalItemFailure.initialization
#print axioms Solidity.Yul.LocalItemFailure.booleanItems
#print axioms Solidity.Yul.LocalItemFailure.defaultItems
#print axioms statementPartialWrite
#print axioms initializerPartialWrite
#print axioms grownBooleanTimeout
#print axioms grownDefaultTimeout
#print axioms normalCompletion
#print axioms notRevert
#print axioms unsupportedReturn

end Solidity.Yul.Checks.LocalItemFailure
