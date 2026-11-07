import Solidity.Lowering.P8.SourceAstCompoundTypes

/-! Partial compiler statement conversion in the existing Source body context.
Regression purpose: preserve complete block order, local initialization and
try success/catch bodies for actual LibraryTry syntax. Unsupported statements
fail rather than disappear. Traversal fuel is not a Source execution resource;
no resolution, Source execution, origin or admission is claimed here. -/
namespace Solidity.Lowering.P8.SourceAstStatements
open Lean Solidity.Source
open SourceAstParameters

def optionalExpression (fuel : Nat) (node : Json) : Except String (Syn (.opt .expr)) :=
  match node with
  | .null => .ok .none
  | _ => (SourceAstExpressions.expression fuel node).map Syn.some

/-- Shared block assembly retains every statement in compiler order. -/
def blockWith (readStatement : Json → Except String (Syn (.stmt .body)))
    (node : Json) : Except String (Syn (.block .body)) := do
  unless (← node.getObjValAs? String "nodeType") == "Block" do throw "ordinary block required"
  let nodes ← node.getObjValAs? (Array Json) "statements"
  let statements ← nodes.toList.mapM readStatement
  return .block (syntaxList (statements.map Syn.stmtItem))

def clauseParameters (fuel : Nat) (node : Json) : Except String (List (Syn .param)) := do
  match node.getObjVal? "parameters" with
  | .error _ | .ok .null => return []
  | .ok parameters =>
    unless (← parameters.getObjValAs? String "nodeType") == "ParameterList" do
      throw "clause parameter list required"
    let values ← parameters.getObjValAs? (Array Json) "parameters"
    values.toList.mapM (SourceAstCompoundTypes.parameterWith (SourceAstCompoundTypes.typeName fuel))

/-- Catch signatures and bodies retain their written names and qualifiers. -/
def catchWith (fuel : Nat) (readBlock : Json → Except String (Syn (.block .body)))
    (node : Json) : Except String (Syn (.catchClause .body)) := do
  unless (← node.getObjValAs? String "nodeType") == "TryCatchClause" do
    throw "try/catch clause required"
  let name ← node.getObjValAs? String "errorName"
  let parameters ← clauseParameters fuel node
  let body ← readBlock (← node.getObjVal? "block")
  match parameters with
  | [] =>
    unless name.isEmpty do throw "named catch requires parameters"
    return .catchPlain body
  | head :: tail =>
    return .catchSig (if name.isEmpty then none else some name) head (syntaxList tail) body

def statement : Nat → Json → Except String (Syn (.stmt .body))
  | 0, _ => .error "statement conversion depth exhausted"
  | fuel + 1, node => do
    match ← node.getObjValAs? String "nodeType" with
    | "Block" => return .blockStmt (← blockWith (statement fuel) node)
    | "ExpressionStatement" => return .simpleStmt (.exprStmt
        (← SourceAstExpressions.expression fuel (← node.getObjVal? "expression")))
    | "Return" => return .returnStmt (← optionalExpression fuel (← node.getObjVal? "expression"))
    | "IfStatement" =>
      let condition ← SourceAstExpressions.expression fuel (← node.getObjVal? "condition")
      let yes ← statement fuel (← node.getObjVal? "trueBody")
      let other ← node.getObjVal? "falseBody"
      let no : Syn (.opt (.stmt .body)) ← match other with
        | .null => pure Syn.none
        | _ => (statement fuel other).map Syn.some
      return .ifStmt condition yes no
    | "VariableDeclarationStatement" =>
      let declarations ← node.getObjValAs? (Array Json) "declarations"
      let [declaration] := declarations.toList | throw "tuple declaration conversion not implemented"
      unless (← declaration.getObjValAs? String "nodeType") == "VariableDeclaration" do
        throw "local declaration required"
      let ty ← SourceAstCompoundTypes.typeName fuel (← declaration.getObjVal? "typeName")
      let loc ← SourceAstTypes.location (← declaration.getObjValAs? String "storageLocation")
      let name ← declaration.getObjValAs? String "name"
      return .simpleStmt (.declVar (.varDecl ty loc name)
        (← optionalExpression fuel (← node.getObjVal? "initialValue")))
    | "TryStatement" =>
      let call ← SourceAstExpressions.expression fuel (← node.getObjVal? "externalCall")
      let clauses ← node.getObjValAs? (Array Json) "clauses"
      let success :: firstCatch :: otherCatches := clauses.toList
        | throw "try requires success and at least one catch"
      unless (← success.getObjValAs? String "nodeType") == "TryCatchClause" &&
          (← success.getObjValAs? String "errorName").isEmpty do
        throw "success clause required first"
      let returns ← clauseParameters fuel success
      let body ← blockWith (statement fuel) (← success.getObjVal? "block")
      let handler := catchWith fuel (blockWith (statement fuel))
      return .tryStmt call (syntaxList returns) body (← handler firstCatch)
        (syntaxList (← otherCatches.mapM handler))
    | _ => throw "statement conversion not implemented"

def block (fuel : Nat) : Json → Except String (Syn (.block .body)) :=
  blockWith (statement fuel)

theorem zero_depth (node : Json) :
    statement 0 node = .error "statement conversion depth exhausted" := rfl

/-- info: 'Solidity.Lowering.P8.SourceAstStatements.statement' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms statement
/-- info: 'Solidity.Lowering.P8.SourceAstStatements.block' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms block
/-- info: 'Solidity.Lowering.P8.SourceAstStatements.zero_depth' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms zero_depth
end Solidity.Lowering.P8.SourceAstStatements
