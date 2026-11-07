import Solidity.Lowering.P8.SourceAstParameters
import Solidity.Frontend.Checked.Lexer

/-! Compiler expression conversion into the existing indexed Source grammar.
Regression purpose: retain receiver/storage alias spelling, tuple order and
literal bytes for LibraryTry bodies. Fuel bounds conversion traversal only;
exhaustion is a conversion gap, not a Source resource or admission premise.
This component does not resolve names, bind artifacts or prove execution. -/
namespace Solidity.Lowering.P8.SourceAstExpressions
open Lean Solidity.Source
open SourceAstParameters

/-- Read decoded compiler bytes using the existing checked hex decoder.
Compiler hexValue admits no separators, unlike source hex literals. -/
def literal (node : Json) : Except String Lit := do
  match ← node.getObjValAs? String "kind" with
  | "string" | "unicodeString" | "hexString" =>
    let raw := (← node.getObjValAs? String "hexValue").toUTF8.toList
    unless raw.all Solidity.Frontend.Checked.isHexDigit do throw "invalid literal hex digits"
    let some bytes := Solidity.Frontend.Checked.hexBody raw | throw "invalid literal hex pairs"
    match ← node.getObjValAs? String "kind" with
    | "unicodeString" => return .unicodeStr bytes
    | "hexString" => return .hexStr bytes
    | _ => return .str bytes
  | "number" =>
    match node.getObjVal? "subdenomination" with
    | .ok .null | .error _ | .ok (.str "") => pure ()
    | _ => throw "unit literal conversion not implemented"
    let raw := (← node.getObjValAs? String "value").toUTF8.toList
    let some value := Solidity.Frontend.Checked.canonNat raw
      | throw "noncanonical integer literal conversion not implemented"
    return .num (.dec value 0 0)
  | "bool" =>
    match ← node.getObjValAs? String "value" with
    | "true" => return .bool true
    | "false" => return .bool false
    | _ => throw "invalid boolean literal"
  | _ => throw "literal conversion not implemented"

/-- Generic reader for the expression constructors currently needed by the
actual compiler fixtures. Unsupported operators/named calls fail explicitly. -/
def expression : Nat → Json → Except String (Syn .expr)
  | 0, _ => .error "expression conversion depth exhausted"
  | fuel + 1, node => do
    match ← node.getObjValAs? String "nodeType" with
    | "Identifier" => return .ident (← node.getObjValAs? String "name")
    | "Literal" => return .lit (← literal node)
    | "MemberAccess" =>
      return .member (← expression fuel (← node.getObjVal? "expression"))
        (← node.getObjValAs? String "memberName")
    | "FunctionCall" =>
      unless (← node.getObjValAs? String "kind") == "functionCall" do
        throw "conversion/struct call not implemented"
      let names ← node.getObjValAs? (Array String) "names"
      unless names.isEmpty do throw "named call conversion not implemented"
      let fn ← expression fuel (← node.getObjVal? "expression")
      let args ← node.getObjValAs? (Array Json) "arguments"
      return .call fn (.positional (syntaxList (← args.toList.mapM (expression fuel))))
    | "Assignment" =>
      unless (← node.getObjValAs? String "operator") == "=" do
        throw "compound assignment conversion not implemented"
      return .assign .assign (← expression fuel (← node.getObjVal? "leftHandSide"))
        (← expression fuel (← node.getObjVal? "rightHandSide"))
    | "TupleExpression" =>
      unless !(← node.getObjValAs? Bool "isInlineArray") do
        throw "inline array conversion not implemented"
      let components ← node.getObjValAs? (Array Json) "components"
      let values ← components.toList.mapM (fun child => do
        match child with
        | .null => pure (Syn.none : Syn (.opt .expr))
        | _ => return Syn.some (← expression fuel child))
      match values with
      | [] => throw "empty tuple conversion not implemented"
      | head :: tail => return .tuple head (syntaxList tail)
    | _ => throw "expression node conversion not implemented"

theorem depth_zero (node : Json) :
    expression 0 node = .error "expression conversion depth exhausted" := rfl

/-- info: 'Solidity.Lowering.P8.SourceAstExpressions.literal' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms literal
/-- info: 'Solidity.Lowering.P8.SourceAstExpressions.expression' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms expression
/-- info: 'Solidity.Lowering.P8.SourceAstExpressions.depth_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms depth_zero
end Solidity.Lowering.P8.SourceAstExpressions
