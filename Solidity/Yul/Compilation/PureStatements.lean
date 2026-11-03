import Solidity.Yul.Compilation.PureExpressions
/-! Reuse actual normal-statement certificates and sequence/assignment proofs,
with the full producer Pure expression compiler. No new source state/control,
function convention or source-admission decision is introduced. -/
namespace Solidity.Yul.Compilation.PureStatements
open Backend Scalar
open Solidity.Yul.Closed ProducerStatements
/-- Finite source horizon is preserved exactly through the real evaluator.
Other statement constructors refuse here, not at Solidity admission. -/
def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) :
    Option (Compiled fuel stmt) :=
  match fuel with
  | 0 => none
  | fuel+1 => by
      apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
        match F,X with
        | [],[] => Option (Compiled (fuel+1) stmt)
        | _,_ => Unit) stmt
      case skip =>
        intro F X c n
        cases F <;> cases X
        · exact some (skip fuel n)
        all_goals exact ()
      case seq =>
        intro F X c n a b
        cases F <;> cases X
        · exact do
            let first ← compile fuel a
            let second ← compile fuel b
            pure (seq first second)
        all_goals exact ()
      case assign =>
        intro F X c n r targets expr
        cases F <;> cases X
        · cases r with
          | zero => exact none
          | succ r =>
            cases r with
            | zero =>
              exact (PureExpressions.compile fuel expr).map (assignTargets targets)
            | succ _ => exact none
        all_goals exact ()
      all_goals intro F X; cases F <;> cases X <;> intros <;> first | exact none | exact ()
termination_by structural fuel

#print axioms compile
end Solidity.Yul.Compilation.PureStatements
