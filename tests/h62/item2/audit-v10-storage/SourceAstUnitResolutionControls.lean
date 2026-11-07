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

/-- Guard initializer/transience and function signature/body retention.
The inputs exercise syntax boundaries, without asserting typing or execution. -/
def stateFunctionChecks : Except String Unit := do
  let leaf (name : String) := Json.mkObj [("nodeType", .str "ElementaryTypeName"), ("name", .str name)]
  let identifier (name : String) := Json.mkObj [("nodeType", .str "Identifier"), ("name", .str name)]
  let stateNode (constant : Bool) := Json.mkObj [("nodeType", .str "VariableDeclaration"),
    ("stateVariable", .bool true), ("constant", .bool constant), ("mutability", .str "mutable"),
    ("storageLocation", .str "default"), ("typeName", leaf "uint256"),
    ("visibility", .str "public"), ("transient", .bool true), ("name", .str "saved"),
    ("value", identifier "seed")]
  match ← part 8 (stateNode false) with
  | .stateVar (.elem (.int false 256 _)) (some .pub) none none true "saved"
      (.some (.ident "seed")) => pure ()
  | _ => throw "state initializer or qualifier changed"
  match part 8 (stateNode true) with
  | .error "mutable state declaration required" => pure ()
  | _ => throw "constant state refusal changed"
  let param (name ty loc : String) := Json.mkObj [("nodeType", .str "VariableDeclaration"),
    ("name", .str name), ("typeName", leaf ty), ("storageLocation", .str loc)]
  let params (entries : Array Json) := Json.mkObj [("nodeType", .str "ParameterList"),
    ("parameters", .arr entries)]
  let fnNode (body : Json) := Json.mkObj [("nodeType", .str "FunctionDefinition"),
    ("kind", .str "function"), ("parameters", params #[param "flag" "bool" "default"]),
    ("returnParameters", params #[param "message" "string" "memory"]),
    ("body", body), ("name", .str "f"), ("visibility", .str "external"),
    ("stateMutability", .str "view"), ("virtual", .bool true)]
  let checkFunction (body : Json) : Except String (Syn (.opt (.block .body))) := do
    match ← part 8 (fnNode body) with
    | .function (.ident "f") (.cons (.param (.elem .bool) none (some "flag")) .nil)
        (some .external) (some .view) .nil true none
        (.cons (.param (.elem .string) (some .memory) (some "message")) .nil) converted =>
        pure converted
    | _ => throw "function signature or qualifiers changed"
  match ← checkFunction .null with
  | .none => pure ()
  | _ => throw "absent function body changed"
  let body := Json.mkObj [("nodeType", .str "Block"), ("statements", .arr #[Json.mkObj [
    ("nodeType", .str "Return"), ("expression", identifier "flag")]])]
  match ← checkFunction body with
  | .some (.block (.cons (.stmtItem (.returnStmt (.some (.ident "flag")))) .nil)) => pure ()
  | _ => throw "function body was discarded or rewritten"

/-- Guard top-level category, abstract flag, ordered children and propagated refusal.
Pragma literals remain tokens; these checks assert no compiler or Source validity. -/
def topChecks : Except String Unit := do
  let member := Json.mkObj [("nodeType", .str "VariableDeclaration"), ("name", .str "flag"),
    ("typeName", Json.mkObj [("nodeType", .str "ElementaryTypeName"), ("name", .str "bool")])]
  let child (name : String) := Json.mkObj [("nodeType", .str "StructDefinition"),
    ("name", .str name), ("members", .arr #[member])]
  let topNode (category : String) (abstract : Bool) (nodes : Array Json) := Json.mkObj [
    ("nodeType", .str "ContractDefinition"), ("name", .str "Owner"),
    ("contractKind", .str category), ("abstract", .bool abstract), ("nodes", .arr nodes)]
  let checkParts (parts : Syn (.list (.part false))) : Except String Unit :=
    match parts with
    | .cons (.struct "First" (.structMember (.elem .bool) "flag") .nil)
        (.cons (.struct "Second" (.structMember (.elem .bool) "flag") .nil) .nil) => .ok ()
    | _ => .error "top-level declaration order changed"
  for (category, abstract) in [("library", false), ("contract", true), ("interface", false)] do
    let converted ← top 8 (topNode category abstract #[child "First", child "Second"])
    match category, converted with
    | "library", .library "Owner" parts => checkParts parts
    | "contract", .contract true "Owner" .none .nil parts => checkParts parts
    | "interface", .interface "Owner" .nil parts => checkParts parts
    | _, _ => throw "top-level category or abstract flag changed"
  match top 8 (topNode "library" true #[]) with
  | .error "abstract library is not syntax" => pure ()
  | _ => throw "abstract library refusal changed"
  match top 8 (topNode "unknown" false #[]) with
  | .error "contract kind required" => pure ()
  | _ => throw "unknown contract category refusal changed"
  match top 8 (topNode "contract" false #[Json.mkObj [("nodeType", .str "Unsupported")]]) with
  | .error "declaration conversion not implemented" => pure ()
  | _ => throw "failed declaration was dropped"
  let tokens := ["solidity", ">=", "0.8.0"]
  let pragmaNode := Json.mkObj [("nodeType", .str "PragmaDirective"),
    ("literals", toJson tokens)]
  match ← top 8 pragmaNode with
  | .pragma actual => unless actual == tokens do throw "pragma tokens changed"
  | _ => throw "pragma category changed"

#eval do
  match topChecks with
  | .ok () => pure ()
  | .error why => throw (IO.userError why)
  match stateFunctionChecks with
  | .ok () => pure ()
  | .error why => throw (IO.userError why)
  match declarationChecks with
  | .ok () => pure ()
  | .error why => throw (IO.userError why)
  for (file, pipeline) in fixtureInputs do
    let raw ← IO.FS.readFile file
    match (do inspect (← Json.parse raw) pipeline) with
    | .ok _ => IO.println s!"{file}: complete unit conversion and eight Source identities passed"
    | .error why => throw (IO.userError why)
end H62.StorageAudit.SourceAstUnitControls
