import Solidity.Yul.LocalPostHorizon
import Solidity.Yul.Checks.LocalLoopFailure

namespace Solidity.Yul.Checks.LocalPostHorizon

def bodyWitness : Nonempty (LocalDefaultItems.Supported Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env [] false ⟨true,false⟩ Solidity.Yul.Checks.LocalDefaultPostIter.items) := ⟨Solidity.Yul.Checks.LocalDefaultPostIter.proof⟩
def stepWitness : Nonempty (LocalBoolControl.Supported Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys Solidity.Yul.Checks.LocalDefaultPostIter.postFaultExpr) := ⟨Solidity.Yul.Checks.LocalDefaultPostIter.postFault⟩

def rawConcrete (fuel : Nat) (state : LocalState Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys) :=
 Solidity.Yul.LocalPostHorizon.omittedPostTimeout Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env [] false false Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys Solidity.Yul.Checks.LocalDefaultPostIter.Out Solidity.Yul.Checks.LocalDefaultPostIter.postFaultExpr Solidity.Yul.Checks.LocalDefaultPostIter.postFault Solidity.Yul.Checks.LocalDefaultPostIter.items Solidity.Yul.Checks.LocalDefaultPostIter.proof fuel state

def sourceConcrete (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env.layout Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env) :=
 Solidity.Yul.LocalPostHorizon.sourcePostTimeout Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env [] false false Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys Solidity.Yul.Checks.LocalDefaultPostIter.Out (.bool false) Solidity.Yul.Checks.LocalDefaultPostIter.postFalse Solidity.Yul.Checks.LocalDefaultPostIter.items Solidity.Yul.Checks.LocalDefaultPostIter.proof glob frame fuel nps ph locals world

theorem falsePostTimeout : Solidity.Yul.LocalDefaultNoGuard.run Solidity.Yul.Checks.LocalDefaultPostIter.postFalse Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultPostIter.afterFalsePostBody := by
  rfl

theorem partialPostWrite : Solidity.Yul.LocalDefaultNoGuard.run Solidity.Yul.Checks.LocalDefaultPostIter.postFault Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .halted .timeout (Solidity.Yul.Checks.LocalDefaultPostIter.assigned true) := by
  rfl

theorem falseGuardSkipsPost : Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostIter.stopTest Solidity.Yul.Checks.LocalDefaultPostIter.postFault Solidity.Yul.Checks.LocalDefaultPostIter.proof 2 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .normal Solidity.Yul.Checks.LocalDefaultPostIter.initial := by
  rfl

theorem doWhileBodyFirstTimeout : Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDefaultPostIter.stopTest Solidity.Yul.Checks.LocalDefaultPostIter.proof 2 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultPostIter.initial := by
  rfl

theorem doWhileFalseCompletes : Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDefaultPostIter.stopTest Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .normal (Solidity.Yul.Checks.LocalDefaultPostIter.assigned false) := by
  rfl

theorem notRevert : Solidity.Yul.LocalDefaultNoGuard.run Solidity.Yul.Checks.LocalDefaultPostIter.postFault Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial ≠ .halted (.revert []) (Solidity.Yul.Checks.LocalDefaultPostIter.assigned true) := by
  intro bad; cases bad

theorem equalityStepRefused : ¬ Nonempty (Solidity.Yul.LocalBoolControl.Supported Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys (.binary .eq (.bool true) (.bool false))) := by
  rintro ⟨proof⟩; cases proof with | base child => cases child

#print axioms Solidity.Yul.LocalPostHorizon.postIteration
#print axioms Solidity.Yul.LocalPostHorizon.doWhileLoop
#print axioms Solidity.Yul.LocalPostHorizon.omittedPostTimeout
#print axioms Solidity.Yul.LocalPostHorizon.sourcePostTimeout
#print axioms falsePostTimeout
#print axioms partialPostWrite
#print axioms falseGuardSkipsPost
#print axioms doWhileBodyFirstTimeout
#print axioms doWhileFalseCompletes
#print axioms notRevert
#print axioms equalityStepRefused

end Solidity.Yul.Checks.LocalPostHorizon
