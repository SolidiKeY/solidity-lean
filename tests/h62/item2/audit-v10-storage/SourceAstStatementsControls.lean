import Solidity.Lowering.P8.SourceAstTryCorrespondence
import Solidity.Source.Ctor

/-! Runtime checks of all four existing LibraryTry function bodies per pipeline.
Regression purpose: retain ordered prefixes, dirty storage receiver, success
returns and Error(string memory) handlers, plus absent return/initializer syntax.
Absent-else, catch boundaries and ordered multi-handler try syntax are guarded too.
Generic syntax cases are not valid-program witnesses. Conversion is not elaboration,
Source execution, artifact origin or H24 admission. -/
namespace H62.StorageAudit.SourceAstStatementsControls
open Lean Solidity.Source Solidity.Lowering.P8.SourceAstStatements

def prefixEight : Syn (.block .body) → Bool
  | .block (.cons (.stmtItem (.simpleStmt (.declVar
      (.varDecl (.elem (.int false 256 _)) none "x")
      (.some (.lit (.num (.dec 8 0 0)))))))
      (.cons (.stmtItem (.tryStmt _ _ _ _ _)) .nil)) => true
  | _ => false

def failureResult : Syn .expr → Bool
  | .tuple (.some (.lit (.num (.dec 19 0 0))))
      (.cons (.some (.ident "message")) .nil) => true
  | _ => false

def errorBody : Syn (.block .body) → Bool
  | .block (.cons (.stmtItem (.returnStmt (.some value))) .nil) => failureResult value
  | _ => false

def handlerShape : Syn (.catchClause .body) → Bool
  | .catchSig (some "Error") (.param (.elem .string) (some .memory) (some "message"))
      .nil body => errorBody body
  | _ => false

def tryShape : Syn (.stmt .body) → Bool
  | .tryStmt (.call (.member (.ident "t") "stru") _) _ _ handler .nil => handlerShape handler
  | _ => false

def dirtyThenTry : Syn (.block .body) → Bool
  | .block (.cons (.stmtItem (.simpleStmt (.exprStmt (.assign .assign
      (.member (.ident "t") "x") (.lit (.num (.dec 9 0 0)))))))
      (.cons (.stmtItem next) .nil)) => tryShape next
  | _ => false

def tryOrder : Syn (.stmt .body) → Bool
  | .tryStmt (.call (.ident "f") (.positional .nil)) .nil (.block .nil)
      (.catchSig (some "Error") (.param (.elem .string) (some .memory) (some "reason"))
        .nil (.block .nil)) (.cons (.catchPlain (.block .nil)) .nil) => true
  | _ => false

def inspect (doc : Json) : Except String Unit := do
  let ast ← doc.getObjVal? "ast"
  let top ← ast.getObjValAs? (Array Json) "nodes"
  let mut bodies : List (Syn (.block .body)) := []
  let mut fSeen := false
  let mut gSeen := false
  for contract in top do
    if (contract.getObjValAs? String "nodeType").toOption == some "ContractDefinition" then
      for node in ← contract.getObjValAs? (Array Json) "nodes" do
        if (node.getObjValAs? String "nodeType").toOption == some "FunctionDefinition" then
          let converted ← block 128 (← node.getObjVal? "body")
          bodies := converted :: bodies
          if (contract.getObjValAs? String "name").toOption == some "C" then
            if (node.getObjValAs? String "name").toOption == some "f" then
              fSeen := prefixEight converted
            if (node.getObjValAs? String "name").toOption == some "g" then
              gSeen := dirtyThenTry converted
  unless bodies.length == 4 && fSeen && gSeen do throw "body census or prefix/handler changed"
  let nodes := bodies.flatMap Syn.nodes
  for (ctor, expected) in [(Ctor.ifStmt, 2), (.tryStmt, 2), (.catchSig, 2),
      (.returnStmt, 6), (.assign, 1), (.call, 4)] do
    unless (nodes.filter (fun n => n.ctor == ctor)).length == expected do
      throw "body constructor census changed"

def refusals : Except String Unit := do
  for raw in [
    "{\"nodeType\":\"WhileStatement\"}",
    "{\"nodeType\":\"TryStatement\",\"externalCall\":{\"nodeType\":\"Identifier\",\"name\":\"f\"},\"clauses\":[]}",
    "{\"nodeType\":\"VariableDeclarationStatement\",\"declarations\":[]}",
    "{\"nodeType\":\"Return\"}"] do
    unless !(statement 128 (← Json.parse raw)).isOk do throw "invalid/unsupported statement accepted"
  let empty := Json.mkObj [("nodeType", .str "Block"), ("statements", .arr #[])]
  unless (block 128 empty).isOk && !(statement 0 empty).isOk do throw "empty/depth boundary changed"

  -- Optional syntax boundaries: no value-return or initializer may be invented.
  let bareReturn := Json.mkObj [("nodeType", .str "Return"), ("expression", .null)]
  match ← statement 128 bareReturn with
  | .returnStmt .none => pure ()
  | _ => throw "bare return gained a value"
  let declaration := Json.mkObj [("nodeType", .str "VariableDeclaration"),
    ("typeName", Json.mkObj [("nodeType", .str "ElementaryTypeName"), ("name", .str "uint256")]),
    ("storageLocation", .str "default"), ("name", .str "fresh")]
  let uninitialized := Json.mkObj [("nodeType", .str "VariableDeclarationStatement"),
    ("declarations", .arr #[declaration]), ("initialValue", .null)]
  match ← statement 128 uninitialized with
  | .simpleStmt (.declVar (.varDecl (.elem (.int false 256 _)) none "fresh") .none) => pure ()
  | _ => throw "local declaration or absent initializer changed"

  -- Absent branches/catch names stay absent; these are syntax-only fixtures.
  let condition := Json.mkObj [("nodeType", .str "Literal"), ("kind", .str "bool"), ("value", .str "true")]
  let branch := Json.mkObj [("nodeType", .str "IfStatement"), ("condition", condition),
    ("trueBody", empty), ("falseBody", .null)]
  match ← statement 128 branch with
  | .ifStmt (.lit (.bool true)) (.blockStmt (.block .nil)) .none => pure ()
  | _ => throw "absent else or conditional body changed"
  let plain := Json.mkObj [("nodeType", .str "TryCatchClause"), ("errorName", .str ""),
    ("parameters", .null), ("block", empty)]
  match ← catchWith 128 (block 128) plain with
  | .catchPlain (.block .nil) => pure ()
  | _ => throw "plain catch changed"
  let rawParam := Json.mkObj [("nodeType", .str "VariableDeclaration"),
    ("typeName", Json.mkObj [("nodeType", .str "ElementaryTypeName"), ("name", .str "bytes")]),
    ("storageLocation", .str "memory"), ("name", .str "raw")]
  let unnamed := Json.mkObj [("nodeType", .str "TryCatchClause"), ("errorName", .str ""),
    ("parameters", Json.mkObj [("nodeType", .str "ParameterList"), ("parameters", .arr #[rawParam])]),
    ("block", empty)]
  match ← catchWith 128 (block 128) unnamed with
  | .catchSig none (.param (.elem .bytes) (some .memory) (some "raw")) .nil (.block .nil) => pure ()
  | _ => throw "unnamed catch signature changed"

  -- The success clause must stay separate from ordered handlers.
  let reason := Json.mkObj [("nodeType", .str "VariableDeclaration"),
    ("typeName", Json.mkObj [("nodeType", .str "ElementaryTypeName"), ("name", .str "string")]),
    ("storageLocation", .str "memory"), ("name", .str "reason")]
  let named := Json.mkObj [("nodeType", .str "TryCatchClause"), ("errorName", .str "Error"),
    ("parameters", Json.mkObj [("nodeType", .str "ParameterList"), ("parameters", .arr #[reason])]),
    ("block", empty)]
  let call := Json.mkObj [("nodeType", .str "FunctionCall"), ("kind", .str "functionCall"),
    ("names", .arr #[]), ("arguments", .arr #[]),
    ("expression", Json.mkObj [("nodeType", .str "Identifier"), ("name", .str "f")])]
  let tryNode (clauses : Array Json) := Json.mkObj [("nodeType", .str "TryStatement"),
    ("externalCall", call), ("clauses", .arr clauses)]
  unless tryOrder (← statement 128 (tryNode #[plain, named, plain])) do
    throw "try success or handler order changed"
  unless !(statement 128 (tryNode #[plain])).isOk do throw "missing first catch accepted"

#eval do
  match refusals with
  | .ok _ => pure ()
  | .error why => throw (IO.userError why)
  for file in ["tests/solc/LibraryTry.ast.json", "tests/solc/LibraryTryIR.ast.json"] do
    let raw ← IO.FS.readFile file
    match (do inspect (← Json.parse raw)) with
    | .ok _ => IO.println s!"{file}: four complete statement bodies converted"
    | .error why => throw (IO.userError why)
end H62.StorageAudit.SourceAstStatementsControls
