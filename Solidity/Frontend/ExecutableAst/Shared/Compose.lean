import Solidity.Frontend.ExecutableAst.Memory.Reader
import Solidity.Frontend.ExecutableAst.ControlTuple.Adapter

/-! One executable callback composition for producer-owned memory and control
packets. Dispatch depends on compiler node shape; recursive children always use
these same callbacks and errors propagate directly. Existing primitive paths and
state-root parsing retain Shared behavior. Raw callbacks are decoding inputs;
public Shared.function/contract perform the selected function checks and root well-formedness/uniqueness validation. -/
namespace Solidity.Frontend.ExecutableAst.Shared
open Lean Solidity.Frontend

private def memoryLocal (j : Json) : Bool :=
  let ds := J.arrD j "declarations"
  if ds.size != 1 then false else
  let d := ds[0]!
  let ty := (J.opt d "typeName").getD .null
  ["ArrayTypeName", "Mapping"].contains (J.kind ty) ||
    ["memory", "storage", "calldata"].contains ((J.str? d "storageLocation").getD "default")

/-- Tuple values and explicit allocation calls extend the existing expression
reader; other calls retain their original refusal. No failure is retried. -/
partial def executableExpression (j : Json) : Except String RawExpr := do
  let kind ← node j
  if kind == "TupleExpression" then
    return ← ControlTuple.expressionStep executableExpression j
  if kind == "FunctionCall" &&
      ((J.opt j "expression").map J.kind) == some "NewExpression" then
    return ← Memory.expressionStep executableExpression Memory.typeName j
  Shared.expressionStep executableExpression j

/-- Reference locals use B's strict location-aware type reader. Primitive and tuple
locals retain source narrow spellings through Shared.localTypeName. -/
partial def executableStatements (j : Json) : Except String (List RawStmt) := do
  if (← node j) == "VariableDeclarationStatement" && memoryLocal j then
    return ← Memory.statementsStep executableExpression executableStatements Memory.typeName j
  ControlTuple.statementsStep executableExpression executableStatements Shared.localValueTypeName j

/-- Canonical executable reader for runtime entrypoints and producer migration.
Reference parameters and returns retain the existing Shared refusal gates. -/
def executableReader : Reader :=
  { Shared.reader with expression := executableExpression, statements := executableStatements }

end Solidity.Frontend.ExecutableAst.Shared
