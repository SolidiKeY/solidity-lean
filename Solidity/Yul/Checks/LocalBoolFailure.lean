import Solidity.Yul.LocalBoolFailure
import Solidity.Yul.Checks.LocalDefaultPostIter

namespace Solidity.Yul.Checks.LocalBoolFailure

def witness : Nonempty (LocalBoolControl.Supported Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys Solidity.Yul.Checks.LocalDefaultPostIter.postFaultExpr) := ⟨Solidity.Yul.Checks.LocalDefaultPostIter.postFault⟩

def concrete (fuel : Nat) (state : LocalState Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys) (halt : Solidity.Source.Halt) :=
  Solidity.Yul.LocalBoolFailure.control Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys Solidity.Yul.Checks.LocalDefaultPostIter.postFaultExpr Solidity.Yul.Checks.LocalDefaultPostIter.postFault fuel state halt

theorem partialWrite : Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalDefaultPostIter.postFault 8 Solidity.Yul.Checks.LocalDefaultPostIter.initial = (.error .timeout, Solidity.Yul.Checks.LocalDefaultPostIter.assigned true) := by
  rfl

theorem shortCircuit : Solidity.Yul.LocalBoolControl.eval (.or (.base (.local .here)) Solidity.Yul.Checks.LocalDefaultPostIter.postFault) 2 Solidity.Yul.Checks.LocalDefaultPostIter.initial = (.ok (Solidity.Yul.Checks.LocalDefaultPostIter.initial.1.get .here),Solidity.Yul.Checks.LocalDefaultPostIter.initial) := by
  rfl

theorem conditionalSkip : Solidity.Yul.LocalBoolControl.eval (.cond (.base (.literal false)) Solidity.Yul.Checks.LocalDefaultPostIter.postFault (.base (.local .here))) 2 Solidity.Yul.Checks.LocalDefaultPostIter.initial = (.ok (Solidity.Yul.Checks.LocalDefaultPostIter.initial.1.get .here),Solidity.Yul.Checks.LocalDefaultPostIter.initial) := by
  rfl

theorem notRevert : (Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalDefaultPostIter.postFault 8 Solidity.Yul.Checks.LocalDefaultPostIter.initial).1 ≠ .error (.revert []) := by
  intro bad; cases bad

theorem unsupportedBase : ¬ Nonempty (Solidity.Yul.LocalBoolExpr.Supported Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys (.binary .and (.bool true) (.bool false))) := by
  rintro ⟨proof⟩; cases proof

#print axioms Solidity.Yul.LocalBoolFailure.expression
#print axioms Solidity.Yul.LocalBoolFailure.control
#print axioms partialWrite
#print axioms shortCircuit
#print axioms conditionalSkip
#print axioms notRevert
#print axioms unsupportedBase

end Solidity.Yul.Checks.LocalBoolFailure
