import Solidity.Frontend.Testing

/-! Import-free executable entry point. Compiler JSON is decoded to the existing
surface syntax, then the existing intrinsic elaborator constructs `Fml C []`.
Unsupported input returns a gap; it is never treated as a successful check. -/
namespace Solidity.Tools.DirectRuntime
open Lean Solidity.Frontend

private def field (j : Json) (s : String) : Except String Json := j.getObjVal? s
private def str (j : Json) (s : String) : Except String String := j.getObjValAs? String s
private def arr (j : Json) (s : String) : Except String (Array Json) := j.getObjValAs? (Array Json) s
private def arrDefault (j : Json) (s : String) : Except String (Array Json) :=
  match j.getObjVal? s with | .error _ => pure #[] | .ok v => v.getArr?
private def node (j : Json) : Except String String := str j "nodeType"
private def optional (j : Json) (s : String) : Option Json :=
  match j.getObjVal? s with | .ok .null => none | .ok v => some v | _ => none
private def prim (j : Json) : Except String Ty := do
  let t ← str (← field j "typeDescriptions") "typeString"
  match t with
  | "uint256" => return .prim .uint
  | "int256" => return .prim .int
  | "bool" => return .prim .bool
  | _ => throw s!"compact verifier: unsupported type {t}"

private partial def expression (j : Json) : Except String RawExpr := do
  let kind ← node j
  let type := ((j.getObjVal? "typeDescriptions").toOption.bind fun d => (d.getObjValAs? String "typeString").toOption).getD ""
  if kind != "Literal" && type.isEmpty then throw "missing expression type"
  if kind != "Literal" && ((type.splitOn "_const").length > 1) then
    throw "compile-time constant expression uses the full rational constant reader"
  match kind with
  | "Literal" =>
    match ← str j "kind" with
    | "bool" => return .bool ((← str j "value") == "true")
    | "number" =>
      -- Constant expressions, units and nondecimal spelling use the full reader.
      if (optional j "subdenomination").isSome then throw "literal units"
      let s ← str j "value"
      let some n := s.toNat? | throw "nondecimal literal"
      return .num n
    | _ => throw "literal kind"
  | "Identifier" => return .name (← str j "name")
  | "BinaryOperation" =>
    let some op := BinOp.ofSym? (← str j "operator") | throw "binary operator"
    return .binop op (← expression (← field j "leftExpression")) (← expression (← field j "rightExpression"))
  | "UnaryOperation" =>
    let op ← match ← str j "operator" with
      | "-" => pure UnOp.neg | "!" => pure UnOp.not | "~" => pure UnOp.bnot
      | _ => throw "unary operator"
    return .unop op (← expression (← field j "subExpression"))
  | "Conditional" =>
    let c ← expression (← field j "condition")
    let a ← expression (← field j "trueExpression")
    let b ← expression (← field j "falseExpression")
    return .ternary c a b
  | _ => throw "compact verifier: unsupported expression"

private partial def statements (j : Json) : Except String (List RawStmt) := do
  match ← node j with
  | "Block" => return [.block (← (← arr j "statements").toList.mapM statements).flatten]
  | "UncheckedBlock" =>
    let body ← (← arr j "statements").toList.mapM statements
    return [.block [.unchecked body.flatten]]
  | "Return" => return [.ret (← (optional j "expression").mapM expression)]
  | "IfStatement" => return [.ite (← expression (← field j "condition"))
      (← statements (← field j "trueBody")) (← match optional j "falseBody" with
        | none => pure [] | some e => statements e)]
  | "VariableDeclarationStatement" =>
    let ds ← arr j "declarations"
    unless ds.size == 1 do throw "tuple declaration"
    let d := ds[0]!
    let t ← prim d
    let .prim p := t | throw "reference declaration"
    return [.decl (.named p.toStr) (← str d "name") (← (optional j "initialValue").mapM expression)]
  | "ExpressionStatement" =>
    let e ← field j "expression"
    match ← node e with
    | "Assignment" =>
      let l ← expression (← field e "leftHandSide")
      let r ← expression (← field e "rightHandSide")
      match ← str e "operator" with
      | "=" => return [.assign l r]
      | op =>
        let some b := BinOp.ofSym? (op.take (op.length - 1)) | throw "assignment operator"
        unless op.endsWith "=" && b.hasCompoundAssign do throw "assignment operator"
        return [.opAssign b l r]
    | "UnaryOperation" =>
      let op ← match ← str e "operator" with
        | "++" => pure IncDec.postInc | "--" => pure IncDec.postDec
        | _ => throw "statement unary operator"
      return [.incDec op (← expression (← field e "subExpression"))]
    | "FunctionCall" =>
      let fn ← field e "expression"
      unless (← node fn) == "Identifier" do throw "call receiver"
      let name ← str fn "name"
      let some identity := (fn.getObjValAs? Int "referencedDeclaration").toOption
        | throw "missing builtin declaration identity"
      unless identity < 0 && (name == "assert" || name == "require") do
        throw "non-builtin call"
      let args ← arr e "arguments"
      unless args.size == 1 do throw "call arguments"
      let condition ← expression args[0]!
      match ← str fn "name" with
      | "assert" => return [.assert condition]
      | "require" => return [.require condition]
      | _ => throw "function call"
    | _ => throw "expression statement"
  | _ => throw "compact verifier: unsupported statement"

private def tokens (s : String) : Except String (List String) := do
  let raw := specTokens s
  if (raw.zip raw.tail).any (fun (a,b) =>
      (a == "\\" && b.toList.any Char.isWhitespace) ||
      ["--", "/-", "-/"].contains (a ++ b)) then
    throw "specification whitespace or comment syntax uses the full parser"
  let rec merge : List String → List String
    | a :: b :: rest => if ["==", "!=", "<=", ">=", "&&", "||", "**"].contains (a ++ b)
      then (a ++ b) :: merge rest else a :: merge (b :: rest)
    | rest => rest
  return (merge raw).filter (fun t => !(t.toList.all Char.isWhitespace))

private def precedence : String → Nat
  | "||" => 1 | "&&" => 2 | "==" | "!=" => 3
  | "<" | ">" | "<=" | ">=" => 4
  | "+" | "-" => 5 | "*" | "/" | "%" => 6 | _ => 0

private partial def specExpr (min : Nat) (ts : List String) : Except String (SpecExpr × List String) := do
  let (left, rest) ← atom ts
  loop left rest none
where
  atom : List String → Except String (SpecExpr × List String)
    | [] => throw "empty specification"
    | "(" :: rest => do
      let (e, rest) ← specExpr 1 rest
      match rest with | ")" :: tail => return (e, tail) | _ => throw "specification parenthesis"
    | "\\" :: "result" :: rest => return (.result, rest)
    | "\\" :: "old" :: "(" :: rest => do
      let (e, rest) ← specExpr 1 rest
      match rest with | ")" :: tail => return (.old e, tail) | _ => throw "old parenthesis"
    | "!" :: rest => do let (e, rest) ← atom rest; return (.unop .not e, rest)
    | "-" :: rest => do let (e, rest) ← atom rest; return (.unop .neg e, rest)
    | "true" :: rest => return (.bool true, rest)
    | "false" :: rest => return (.bool false, rest)
    | s :: rest =>
      if let some n := s.toNat? then return (.num n, rest)
      else if !s.isEmpty && s.toList.all (fun c => c.isAlphanum || c == '_' || c == '$') &&
          !(s.toList.head!).isDigit then return (.name s, rest)
      else throw s!"unsupported specification token {s}"
  loop (left : SpecExpr) (ts : List String) (previous : Option Nat) : Except String (SpecExpr × List String) := do
    match ts with
    | op :: rest =>
      let p := precedence op
      if p < min || p == 0 then return (left, ts)
      if (p == 3 || p == 4) && previous == some p then throw "nonassociative comparison"
      let some b := BinOp.ofSym? op | throw "specification operator"
      let (right, rest) ← specExpr (p + 1) rest
      loop (.binop b left right) rest (some p)
    | [] => return (left, [])

private def specification (j : Json) : Except String FunSpec := do
  let mut out : FunSpec := {}
  for clause in ← keyClauses (docText j) do
    unless clause.kind == "requires" || clause.kind == "ensures" do throw "specification directive"
    let (e, rest) ← specExpr 1 (← tokens clause.text)
    unless rest.isEmpty do throw "unsupported specification suffix"
    if clause.kind == "requires" then out := { out with requires := out.requires ++ [e] }
    else out := { out with ensures := out.ensures ++ [e] }
  return out

private def params (j : Json) (returns : Bool) (fresh : String) : Except String (List (String × Ty)) := do
  (← arr j "parameters").toList.zipIdx.mapM fun (p, i) => do
    let n ← str p "name"
    if n.isEmpty && !returns then throw "unnamed parameter"
    return (if n.isEmpty then s!"{fresh}{i}" else n, ← prim p)

private def function (j : Json) (avoid : String) : Except String (String × FunDecl) := do
  unless (← str j "kind") == "function" && (← arrDefault j "modifiers").isEmpty do throw "constructor or modifiers"
  let spec ← specification j
  let mut fresh := "__solidity_direct_return_"
  while (avoid.splitOn fresh).length > 1 do fresh := fresh ++ "_"
  let ps ← params (← field j "parameters") false fresh
  let rs ← params (← field j "returnParameters") true fresh
  let rawBody ← field j "body"
  unless (← node rawBody) == "Block" do throw "function body"
  let body := (← (← arr rawBody "statements").toList.mapM statements).flatten
  let payable := (← str j "stateMutability") == "payable"
  return (← str j "name", { params := ps, rets := rs, body, spec, payable })

private def contract (j : Json) : Except String Contract := do
  unless (← str j "contractKind") == "contract" && (← arrDefault j "baseContracts").isEmpty do throw "inheritance or interface"
  unless (← keyClauses (docText j)).isEmpty do throw "contract specification"
  let avoid := j.compress
  let mut vars := []
  let mut funs := []
  for n in ← arr j "nodes" do
    match ← node n with
    | "VariableDeclaration" =>
      unless (← str n "mutability") == "mutable" && (optional n "value").isNone do throw "state initializer or constant"
      if (n.getObjValAs? String "storageLocation").toOption == some "transient" then throw "transient storage"
      vars := vars ++ [(← str n "name", ← prim n)]
    | "FunctionDefinition" => funs := funs ++ [← function n avoid]
    | _ => throw "contract member"
  unless (funs.map (·.1)).eraseDups.length == funs.length do throw "overloaded function"
  if h : vars.all (fun nt => nt.2.okDeep) = true then
    if hn : Semantics.nodupKeysB vars = true then
      return { vars, funs, vars_ok := h, vars_nodup := hn }
    else throw "duplicate storage root"
  else throw "ill-formed storage type"

/-- No parser, elaborator environment, proof term or module file is loaded.
The same intrinsic obligation builder and executable verifier are called. -/
def check (request : Json) : Except String Json := do
  let source ← field request "contract"
  let C ← contract source
  let selected := (request.getObjValAs? String "function").toOption
  let listing := (request.getObjValAs? Bool "listing").toOption.getD false
  let mut rows := #[]
  for n in ← arr source "nodes" do
    unless (← node n) == "FunctionDefinition" do continue
    let name ← str n "name"
    if selected.isSome && selected != some name then continue
    let visibility ← str n "visibility"
    unless visibility == "public" || visibility == "external" do throw "internal function selection"
    let some d := Semantics.lookupBy name C.funs | throw "missing function"
    unless !d.spec.ensures.isEmpty || !d.spec.requires.isEmpty do throw "function without specification"
    let φ ← specObligation C name
    let result := if listing then Json.mkObj [("status", toJson "ready"), ("reason", toJson "")]
      else Solidity.Frontend.directResult C φ
    let result := match result.getObjVal? "counterexample" with
      | .error _ => result
      | .ok witness => match witness.getObjValAs? (Array Json) "arguments" with
        | .error _ => result
        | .ok args =>
          let args := args.map fun (arg : Json) =>
            match arg.getObjValAs? String "modelName" with
            | .error _ => arg
            | .ok name => match d.params.findIdx? (fun (p : String × Ty) => p.1 == name) with
              | none => arg
              | some i => arg.setObjVal! "paramIndex" (toJson i)
          result.setObjVal! "counterexample" (witness.setObjVal! "arguments" (toJson args))
    let result := result.setObjVal! "function" (toJson name)
      |>.setObjVal! "sourceId" (← field n "id")
      |>.setObjVal! "verification" (toJson "direct")
      |>.setObjVal! "reading" (toJson "solc")
      |>.setObjVal! "tag" (toJson "specified")
    rows := rows.push result
  if rows.isEmpty then throw "no selected functions"
  return Json.arr rows

@[export solidity_direct_check]
def checkString (input : String) : String :=
  let result := do check (← Json.parse input)
  (match result with
  | .ok rows => Json.mkObj [("results", rows)]
  | .error reason => Json.mkObj [("gap", toJson reason)]).compress

end Solidity.Tools.DirectRuntime
