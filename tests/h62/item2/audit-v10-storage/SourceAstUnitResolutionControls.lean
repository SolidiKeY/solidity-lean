import Solidity.Lowering.P8.SourceAstDeclarationCorrespondence
import Solidity.Source.WellFormed

/-! Conversion/resolution checks independent of the pending full-elaboration
acceptance probe. Regression purpose: preserve the same eight owned catalogue
entries in both actual pipeline inputs. No body typing or origin is claimed. -/
namespace H62.StorageAudit.SourceAstUnitControls
open Lean Solidity.Source
open Solidity.Lowering.P8.SourceAstUnit

def fixtureInputs : List (String × Solidity.Roadmap.Pipeline) :=
  [("tests/solc/LibraryTry.ast.json", .legacy), ("tests/solc/LibraryTryIR.ast.json", .viaIR)]

def inspect (doc : Json) (pipeline : Solidity.Roadmap.Pipeline) : Except String Resolution := do
  let converted ← unit 128 (← doc.getObjVal? "ast")
  let result := resolveUnit { pipeline := pipeline } converted
  let declarations := result.env.decls
  for (scope, name, kind) in [(none, "L", DeclKind.library), (none, "C", .contract),
      (some "L", "S", .struct), (some "L", "integer", .function),
      (some "L", "stru", .function), (some "C", "t", .stateVar),
      (some "C", "f", .function), (some "C", "g", .function)] do
    unless (declarations.filter (fun d => d.scope == scope && d.name == name && d.kind == kind)).length == 1 do
      throw "source declaration ownership changed"
  unless declarations.length == 8 do throw "unexpected Source declaration count"
  return result

/-- Guard member order, nonempty struct refusal and using-path qualifiers.
These are syntax conversion checks, not Source typing or admission witnesses. -/
def declarationChecks : Except String Unit := do
  let member (name ty : String) := Json.mkObj [("nodeType", .str "VariableDeclaration"),
    ("name", .str name), ("typeName", Json.mkObj [("nodeType", .str "ElementaryTypeName"),
      ("name", .str ty)])]
  let structNode (members : Array Json) := Json.mkObj [("nodeType", .str "StructDefinition"),
    ("name", .str "Pair"), ("members", .arr members)]
  match ← part 8 (structNode #[member "flag" "bool", member "count" "uint256"]) with
  | .struct "Pair" (.structMember (.elem .bool) "flag")
      (.cons (.structMember (.elem (.int false 256 _)) "count") .nil) => pure ()
  | _ => throw "struct member order changed"
  match part 8 (structNode #[]) with
  | .error "nonempty struct required" => pure ()
  | _ => throw "empty struct refusal changed"
  let usingNode (ty : Json) (global : Bool) := Json.mkObj [
    ("nodeType", .str "UsingForDirective"), ("libraryName", Json.mkObj [
      ("nodeType", .str "IdentifierPath"), ("name", .str "L")]),
    ("typeName", ty), ("global", .bool global)]
  match ← part 8 (usingNode .null true) with
  | .usingPart (.usingPath ⟨"L", []⟩ .none true) => pure ()
  | _ => throw "untyped global using changed"
  match ← part 8 (usingNode (Json.mkObj [("nodeType", .str "UserDefinedTypeName"),
      ("namePath", .str "L.S")]) false) with
  | .usingPart (.usingPath ⟨"L", []⟩ (.some (.userType ⟨"L", ["S"]⟩)) false) => pure ()
  | _ => throw "typed using identity changed"

#eval do
  match declarationChecks with
  | .ok () => pure ()
  | .error why => throw (IO.userError why)
  for (file, pipeline) in fixtureInputs do
    let raw ← IO.FS.readFile file
    match (do inspect (← Json.parse raw) pipeline) with
    | .ok _ => IO.println s!"{file}: complete unit conversion and eight Source identities passed"
    | .error why => throw (IO.userError why)
end H62.StorageAudit.SourceAstUnitControls
