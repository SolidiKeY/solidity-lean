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
  ProducerStatements.compileWith PureExpressions.compile fuel stmt

#print axioms compile
end Solidity.Yul.Compilation.PureStatements
