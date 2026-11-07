import Solidity.Lowering.P8.SourceAstStatements

/-! Partial declaration/unit reader feeding the existing Source grammar.
Regression purpose: retain library/contract ownership, using directives, state
roots, signatures and original bodies without a hand-written resolved program.
Unsupported declaration forms fail explicitly. Compiler IDs are not Source
positions. Conversion alone supplies no origin, admission or lifecycle proof. -/
namespace Solidity.Lowering.P8.SourceAstUnit
open Lean Solidity.Source
open SourceAstParameters

def absentOrEmpty (node : Json) (key : String) : Except String Unit :=
  match node.getObjVal? key with
  | .error _ | .ok .null | .ok (.arr #[]) => .ok ()
  | _ => .error ("nonempty conversion field not implemented: " ++ key)

def optionalBool (node : Json) (key : String) : Except String Bool :=
  match node.getObjVal? key with
  | .error _ => .ok false
  | .ok value => value.getBool?

def optionalExprField (fuel : Nat) (node : Json) (key : String) :
    Except String (Syn (.opt .expr)) :=
  match node.getObjVal? key with
  | .error _ => .ok .none
  | .ok value => SourceAstStatements.optionalExpression fuel value

def functionVisibility : String → Except String (Option Visibility)
  | "public" => .ok (some .pub)
  | "private" => .ok (some .priv)
  | "internal" => .ok (some .internal)
  | "external" => .ok (some .external)
  | _ => .error "function visibility required"

def stateVisibility : String → Except String (Option StateVis)
  | "public" => .ok (some .pub)
  | "private" => .ok (some .priv)
  | "internal" => .ok (some .internal)
  | _ => .error "state visibility required"

def structMember (fuel : Nat) (node : Json) : Except String (Syn .structMember) := do
  unless (← node.getObjValAs? String "nodeType") == "VariableDeclaration" do
    throw "struct member required"
  return .structMember (← SourceAstCompoundTypes.typeName fuel (← node.getObjVal? "typeName"))
    (← node.getObjValAs? String "name")

def part (fuel : Nat) (node : Json) : Except String (Syn (.part false)) := do
  match ← node.getObjValAs? String "nodeType" with
  | "StructDefinition" =>
    let members ← node.getObjValAs? (Array Json) "members"
    let first :: rest := ← members.toList.mapM (structMember fuel)
      | throw "nonempty struct required"
    return .struct (← node.getObjValAs? String "name") first (syntaxList rest)
  | "FunctionDefinition" =>
    unless (← node.getObjValAs? String "kind") == "function" do
      throw "constructor/fallback conversion not implemented"
    absentOrEmpty node "modifiers"
    absentOrEmpty node "overrides"
    let args ← SourceAstCompoundTypes.parametersWith (SourceAstCompoundTypes.typeName fuel)
      (← node.getObjVal? "parameters")
    let results ← SourceAstCompoundTypes.parametersWith (SourceAstCompoundTypes.typeName fuel)
      (← node.getObjVal? "returnParameters")
    let body ← node.getObjVal? "body"
    let converted : Syn (.opt (.block .body)) ← match body with
      | .null => pure .none
      | _ => (SourceAstStatements.block fuel body).map Syn.some
    return .function (.ident (← node.getObjValAs? String "name")) args
      (← functionVisibility (← node.getObjValAs? String "visibility"))
      (← SourceAstCompoundTypes.mutability (← node.getObjValAs? String "stateMutability"))
      .nil (← optionalBool node "virtual") none results converted
  | "VariableDeclaration" =>
    unless (← node.getObjValAs? Bool "stateVariable") &&
        !(← node.getObjValAs? Bool "constant") &&
        (← node.getObjValAs? String "mutability") == "mutable" &&
        (← node.getObjValAs? String "storageLocation") == "default" do
      throw "mutable state declaration required"
    absentOrEmpty node "overrides"
    return .stateVar (← SourceAstCompoundTypes.typeName fuel (← node.getObjVal? "typeName"))
      (← stateVisibility (← node.getObjValAs? String "visibility")) none none
      (← optionalBool node "transient") (← node.getObjValAs? String "name")
      (← optionalExprField fuel node "value")
  | "UsingForDirective" =>
    absentOrEmpty node "functionList"
    let library ← node.getObjVal? "libraryName"
    unless (← library.getObjValAs? String "nodeType") == "IdentifierPath" do
      throw "library identifier path required"
    let ty ← node.getObjVal? "typeName"
    let converted : Syn (.opt .typeName) ← match ty with
      | .null => pure .none
      | _ => (SourceAstCompoundTypes.typeName fuel ty).map Syn.some
    return .usingPart (.usingPath (← SourceAstTypes.path (← library.getObjValAs? String "name"))
      converted (← node.getObjValAs? Bool "global"))
  | _ => throw "declaration conversion not implemented"

def top (fuel : Nat) (node : Json) : Except String (Syn .top) := do
  match ← node.getObjValAs? String "nodeType" with
  | "PragmaDirective" => return .pragma (← node.getObjValAs? (List String) "literals")
  | "ContractDefinition" =>
    absentOrEmpty node "baseContracts"
    absentOrEmpty node "storageLayout"
    let name ← node.getObjValAs? String "name"
    let parts ← node.getObjValAs? (Array Json) "nodes"
    let converted := syntaxList (← parts.toList.mapM (part fuel))
    let abstract ← optionalBool node "abstract"
    match ← node.getObjValAs? String "contractKind" with
    | "library" =>
      unless !abstract do throw "abstract library is not syntax"
      return .library name converted
    | "contract" => return .contract abstract name .none .nil converted
    | "interface" => return .interface name .nil converted
    | _ => throw "contract kind required"
  | _ => throw "top-level conversion not implemented"

def unit (fuel : Nat) (node : Json) : Except String (Syn .unit) := do
  unless (← node.getObjValAs? String "nodeType") == "SourceUnit" do throw "SourceUnit required"
  let nodes ← node.getObjValAs? (Array Json) "nodes"
  return .unit (syntaxList (← nodes.toList.mapM (top fuel)))

/-- info: 'Solidity.Lowering.P8.SourceAstUnit.part' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms part
/-- info: 'Solidity.Lowering.P8.SourceAstUnit.unit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms unit
end Solidity.Lowering.P8.SourceAstUnit
