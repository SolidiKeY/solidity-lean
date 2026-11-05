import Solidity.Frontend.ExecutableAst.Shared.Translate

/-! # Control and tuple AST adapters

One-step callbacks over A's published Reader boundary. The only emitted syntax
is the existing Raw syntax consumed by the intrinsic elaborator. Errors are
final; calls, nested tuple shapes and inline arrays are never retried elsewhere.
No execution, name resolution, constant evaluator or producer is introduced.
-/
namespace Solidity.Frontend.ExecutableAst.ControlTuple
open Lean (Json)
open Shared

/-- Require an explicit ordinary compiler tuple; null value leaves are errors. -/
def components (j : Json) : Except String (List Json) := do
  unless (← node j) == "TupleExpression" do throw "expected explicit tuple"
  unless (← j.getObjValAs? Bool "isInlineArray") == false do throw "inline array"
  let ty ← str (← field j "typeDescriptions") "typeString"
  unless !ty.isEmpty do throw "missing expression type"
  let cs := (← arr j "components").toList
  unless !cs.isEmpty do throw "empty tuple"
  return cs

/-- A scalar child cannot silently contain a tuple/call or reference value. -/
def scalar (read : Json → Except String RawExpr) (j : Json) : Except String RawExpr := do
  if !constTy j then
    let _ ← Shared.prim j
    pure ()
  let e ← read j
  match e with
  | .tuple _ | .call .. => throw "nested tuple or call"
  | _ => return e

/-- Tuple expressions are values only; target holes are handled separately. -/
def expressionStep (read : Json → Except String RawExpr) (j : Json) : Except String RawExpr := do
  if (← node j) != "TupleExpression" then return ← Shared.expressionStep read j
  let cs ← components j
  match cs with
  | [c] => read c
  | _ => return .tuple (← cs.mapM (scalar read))

/-- Explicit tuple RHS, preserving every value, including discarded positions. -/
def values (read : Json → Except String RawExpr) (n : Nat) (j : Json) : Except String RawExpr := do
  let cs ← components j
  unless cs.length == n do throw "tuple arity mismatch"
  return .tuple (← cs.mapM (scalar read))

/-- A discarded syntactically pure member read need not be total. The
intrinsic tuple elaborator drops pure operands, so retain unknown for this
shape until its typed totality is available through the reader boundary. -/
def preserveDiscarded (slots : List Bool) (rhs : RawExpr) : Except String RawExpr := do
  let .tuple es := rhs | throw "explicit tuple value required"
  unless slots.length == es.length do throw "tuple arity mismatch"
  for (keep, e) in slots.zip es do
    if !keep && e.isPure then
      match e with
      | .num _ | .bool _ | .name _ => pure ()
      | _ => throw "unknown: discarded potentially failing pure read"
  return rhs

/-- Primitive target syntax only; final place/alias checks stay intrinsic. -/
def target (read : Json → Except String RawExpr) (j : Json) : Except String (Option RawExpr) := do
  if j == .null then return none
  unless ["Identifier", "MemberAccess", "IndexAccess"].contains (← node j) do
    throw "tuple target"
  return some (← scalar read j)

/-- Optional tuple declaration slots retain their exact positions. -/
def declaration (readType : Json → Except String (Ty × RawTy)) (j : Json) :
    Except String (Option (RawTy × String)) := do
  if j == .null then return none
  unless (← node j) == "VariableDeclaration" do throw "tuple declaration node"
  let (.prim _, t) ← readType (← field j "typeName") | throw "tuple reference declaration"
  let name ← str j "name"
  unless !name.isEmpty do throw "unnamed tuple declaration"
  return some (t, name)

/-- Emit existing doWhile/tuple syntax; lowerLoop/elabTuple own all semantics. -/
def statementsStep (readExpr : Json → Except String RawExpr)
    (readStmts : Json → Except String (List RawStmt))
    (readType : Json → Except String (Ty × RawTy)) (j : Json) : Except String (List RawStmt) := do
  match ← node j with
  | "DoWhileStatement" =>
    return [.doWhile (← Shared.loopSpec j) (← readStmts (← field j "body"))
      (← readExpr (← field j "condition"))]
  | "VariableDeclarationStatement" =>
    let ds := (← arr j "declarations").toList
    if ds.length == 1 then return ← Shared.statementsStep readExpr readStmts readType j
    unless ds.length >= 2 do throw "empty tuple declaration"
    let vs ← ds.mapM (declaration readType)
    unless vs.any Option.isSome do throw "tuple declaration has no bindings"
    let rhs ← values readExpr ds.length (← field j "initialValue")
    return [.tupleDecl vs (← preserveDiscarded (vs.map Option.isSome) rhs)]
  | "ExpressionStatement" =>
    let e ← field j "expression"
    if (← node e) == "Assignment" then
      let left ← field e "leftHandSide"
      if (← node left) == "TupleExpression" then
        let ls ← components left
        if ls.length >= 2 then
          unless (← str e "operator") == "=" do throw "tuple compound assignment"
          let ts ← ls.mapM (target readExpr)
          unless ts.any Option.isSome do throw "tuple assignment has no targets"
          let rhs ← values readExpr ls.length (← field e "rightHandSide")
          return [.tupleAssign ts (← preserveDiscarded (ts.map Option.isSome) rhs)]
    return ← Shared.statementsStep readExpr readStmts readType j
  | _ => Shared.statementsStep readExpr readStmts readType j

partial def expression (j : Json) : Except String RawExpr := expressionStep expression j
partial def statements (j : Json) : Except String (List RawStmt) :=
  statementsStep expression statements Shared.typeName j

/-- Packet for A's producer integration; no producer is changed in this lane. -/
def reader : Shared.Reader := { Shared.reader with expression, statements }

end Solidity.Frontend.ExecutableAst.ControlTuple
