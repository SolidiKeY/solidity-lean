import Solidity.Calculus.ProgramReduction
import Solidity.Examples.ReadRealization

/-!
# Exact original-program decisions

Supported source statements normalize to certified updates before the
shared typed arithmetic decision. Both verdicts describe the original
starting state, including ordinary box/diamond failure.
-/

namespace Solidity.Examples.ProgramReduction

open Solidity.Decide Solidity.ReadRealization
open Solidity.Examples.ReadRealization (Bank three)
open scoped Solidity.Scoped

local instance : InContract := ⟨Bank⟩

def writeClaim : Fml Bank [] := dl!{ [ balances[3] = 17; ] balances[3] == 17 }
def writeReduction : ParameterReduction writeClaim :=
  (programReduction? writeClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval writeReduction.verify.isLeft

def badWrite : Fml Bank [] := dl!{ [ balances[3] = 17; ] balances[3] == 19 }
def badWriteReduction : ParameterReduction badWrite :=
  (programReduction? badWrite).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval badWriteReduction.verify.isRight

def localClaim : Fml Bank [] :=
  dl!{ [ uint x = balances[3]; x = x - 1; ] x == x }
def localReduction : ParameterReduction localClaim :=
  (programReduction? localClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval localReduction.verify.isLeft

def failingDiamond : Fml Bank [] :=
  dl!{ ⟨ uint x = balances[3]; x = x - 1; ⟩ x == x }
def failingReduction : ParameterReduction failingDiamond :=
  (programReduction? failingDiamond).get (by decide +kernel)

/-- info: some 0 -/
#guard_msgs in
#eval match failingReduction.verify with
  | .inl _ => none
  | .inr cm => some (three.read cm.state.storage).val

def nestedClaim : Fml Bank [] :=
  dl!{ [ uint x = 17; { uint y = 19; y = 23; }; balances[3] = x; ] balances[3] == 17 }
def nestedReduction : ParameterReduction nestedClaim :=
  (programReduction? nestedClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval nestedReduction.verify.isLeft

def defaultLocal : Fml Bank [] := dl!{ ⟨ uint x; ⟩ x == 0 }
def defaultLocalReduction : ParameterReduction defaultLocal :=
  (programReduction? defaultLocal).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval defaultLocalReduction.verify.isLeft

def deleteClaim : Fml Bank [] := dl!{ ⟨ delete balances[3]; ⟩ balances[3] == 0 }
def deleteReduction : ParameterReduction deleteClaim :=
  (programReduction? deleteClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval deleteReduction.verify.isLeft

def branchLocals : Fml Bank [] :=
  dl!{ [ uint x = 17;
    if (paused) { uint y = 19; y = 23; } else { uint z = 29; z = 31; };
    balances[3] = x; ] balances[3] == 17 }
def branchLocalsReduction : ParameterReduction branchLocals :=
  (programReduction? branchLocals).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval branchLocalsReduction.verify.isLeft

def parameterProgram : Fml Bank [] := dl!{ ∀ uint x; [ uint y = x; y = y - 1; ] y < x }
def parameterProgramReduction : ParameterReduction parameterProgram :=
  (programReduction? parameterProgram).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval parameterProgramReduction.verify.isLeft

def requireClaim : Fml Bank [] :=
  dl!{ [ require(balances[3] > 17); ] balances[3] > 17 }
def requireReduction : ParameterReduction requireClaim :=
  (programReduction? requireClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval requireReduction.verify.isLeft

def partialRequireBox : Fml Bank [] :=
  dl!{ balances[3] == 0 → [ require(balances[3] - 1 == 0); ] false }
def partialRequireReduction : ParameterReduction partialRequireBox :=
  (programReduction? partialRequireBox).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval partialRequireReduction.verify.isLeft

def assertionClaim : Fml Bank [] := dl!{ [ assert(balances[3] > 17); ] true }
def assertionReduction : ParameterReduction assertionClaim :=
  (programReduction? assertionClaim).get (by decide +kernel)

/-- info: some 0 -/
#guard_msgs in
#eval match assertionReduction.verify with
  | .inl _ => none
  | .inr cm => some (three.read cm.state.storage).val

def assertionDiamond : Fml Bank [] := dl!{ ⟨ assert(balances[3] > 17); ⟩ true }
def assertionDiamondReduction : ParameterReduction assertionDiamond :=
  (programReduction? assertionDiamond).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval assertionDiamondReduction.verify.isRight

def partialAssertBox : Fml Bank [] :=
  dl!{ balances[3] == 0 → [ assert(balances[3] - 1 == 0); ] false }
def partialAssertReduction : ParameterReduction partialAssertBox :=
  (programReduction? partialAssertBox).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval partialAssertReduction.verify.isLeft

def revertBox : Fml Bank [] := dl!{ [ revert(); ] false }
def revertBoxReduction : ParameterReduction revertBox :=
  (programReduction? revertBox).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval revertBoxReduction.verify.isLeft

def revertDiamond : Fml Bank [] := dl!{ ⟨ revert(); ⟩ true }
def revertDiamondReduction : ParameterReduction revertDiamond :=
  (programReduction? revertDiamond).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval revertDiamondReduction.verify.isRight

def branchClaim : Fml Bank [] :=
  dl!{ [ if (balances[3] > 17) { balances[3] = 19; } else { balances[3] = 23; }; ] balances[3] > 17 }
def branchReduction : ParameterReduction branchClaim :=
  (programReduction? branchClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval branchReduction.verify.isLeft

def badBranch : Fml Bank [] :=
  dl!{ [ if (balances[3] > 17) { balances[3] = 19; } else { balances[3] = 23; }; ] balances[3] == 19 }
def badBranchReduction : ParameterReduction badBranch :=
  (programReduction? badBranch).get (by decide +kernel)

/-- info: some true -/
#guard_msgs in
#eval match badBranchReduction.verify with
  | .inl _ => none
  | .inr cm => some (decide ((three.read cm.state.storage).val ≤ 17))

def ignoredPanic : Fml Bank [] :=
  dl!{ ⟨ if (false) { assert(false); } else { balances[3] = 17; }; ⟩ balances[3] == 17 }
def ignoredPanicReduction : ParameterReduction ignoredPanic :=
  (programReduction? ignoredPanic).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval ignoredPanicReduction.verify.isLeft

def partialBranchBox : Fml Bank [] :=
  dl!{ balances[3] == 0 → [ if (balances[3] - 1 == 0) { } else { }; ] false }
def partialBranchReduction : ParameterReduction partialBranchBox :=
  (programReduction? partialBranchBox).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval partialBranchReduction.verify.isLeft

def partialBranchDiamond : Fml Bank [] :=
  dl!{ balances[3] == 0 → ⟨ if (balances[3] - 1 == 0) { } else { }; ⟩ true }
def partialBranchDiamondReduction : ParameterReduction partialBranchDiamond :=
  (programReduction? partialBranchDiamond).get (by decide +kernel)

/-- info: some 0 -/
#guard_msgs in
#eval match partialBranchDiamondReduction.verify with
  | .inl _ => none
  | .inr cm => some (three.read cm.state.storage).val

def badWriteCountermodel : badWriteReduction.Countermodel :=
  badWriteReduction.countermodelOfCheck () (by decide +kernel)

/-- Writing 17 does not establish the original postcondition `balances[3] == 19`. -/
theorem badWrite_invalid : ¬ Fml.Valid badWrite :=
  fun h => badWriteCountermodel.refutes (h badWriteCountermodel.state)

example : (ProgramNormalization.ofFormula? 0 writeClaim).isNone = true := by decide +kernel

-- A budget of two cannot visit the conjunction and both children.
example : (ProgramNormalization.ofFormula? 2 (dl!{ true ∧ true })).isNone = true := by decide +kernel

def serialBranches : Fml Bank [] :=
  dl!{ [ if (true) { } else { }; if (true) { } else { }; if (true) { } else { }; ] true }

/-- info: true -/
#guard_msgs in #eval (ProgramNormalization.ofFormula? 64 serialBranches).isNone

example : (programReduction? (dl!{ [ while (true) { }; ] true })).isNone = true := by
  decide +kernel

example : (programReduction? (dl!{ [ balances[3] += 1; ] true })).isNone = true := by
  decide +kernel

/-- info: 'Solidity.Upd.afterT_run_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Upd.afterT_run_iff

/-- info: 'Solidity.Examples.ProgramReduction.badWrite_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms badWrite_invalid

end Solidity.Examples.ProgramReduction
