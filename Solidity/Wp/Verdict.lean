import Solidity.Semantics

/-!
# The verdict of a completed execution

`SolidityJudgment.check` runs a block and then reads the postcondition.  The
second half of that — "given how the run ended, what is the verdict?" — is a
function of the result alone, and several layers need it without needing the
rest of the rewrite theory: `Wp/StepSoundness.lean`, which is about a step,
and `Update/Wp.lean`, which is about a taclet's goals.  It lives here so that
neither has to import the other's dependencies.
-/

namespace Solidity
namespace Wp

open Semantics

/-- The verdict `SolidityJudgment.check` computes from a completed
execution result: evaluate the postcondition on success, absorb `revert`
under box, refuse everything else. -/
def checkResult (sm : SolidityModality) (post : WrappedExpr) :
    Res State -> Bool
  | .ok t =>
      match evalValue t post with
      | .ok (_, Value.bool b) => b
      | _ => false
  | .error .revert => sm = SolidityModality.box
  | .error .stuck => false

/-- `SolidityJudgment.check` factors through `checkResult` applied to the
block's execution result. -/
theorem check_eq_checkResult (sm : SolidityModality) (b : Block)
    (post : WrappedExpr) (s : State) :
    (SolidityJudgment.mk ⟨sm, b⟩ post).check s
      = checkResult sm post (execBlock s b) := by
  cases hres : execBlock s b with
  | ok t =>
      cases hval : evalValue t post with
      | ok p =>
          obtain ⟨u, v⟩ := p
          cases v <;>
            simp [SolidityJudgment.check, checkResult, hres, hval]
      | error e =>
          simp [SolidityJudgment.check, checkResult, hres, hval]
  | error e =>
      cases e <;> simp [SolidityJudgment.check, checkResult, hres]

end Wp
end Solidity
