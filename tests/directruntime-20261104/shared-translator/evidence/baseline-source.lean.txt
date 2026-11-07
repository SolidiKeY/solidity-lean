import Solidity.Frontend.Testing
import Solidity.Calculus.AnonLocalCapture

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

private partial def typeName (j : Json) : Except String (Ty × RawTy) := do
  match ← node j with
  | "ElementaryTypeName" =>
    let name ← str j "name"
    let p ← match name with
      | "uint" | "uint256" => pure PrimTy.uint
      | "int" | "int256" => pure PrimTy.int
      | "bool" => pure PrimTy.bool
      | _ => throw s!"compact verifier: unsupported type {name}"
    return (.prim p, .named p.toStr)
  | "ArrayTypeName" =>
    let (t, raw) ← typeName (← field j "baseType")
    if let some len := optional j "length" then
      let some n := (constVal len).bind Q.int? | throw "array length"
      unless n ≥ 0 do throw "negative array length"
      return (.fixed t n.toNat, .fixed raw n.toNat)
    return (.array t, .array raw)
  | "Mapping" =>
    let (.prim k, rk) ← typeName (← field j "keyType") | throw "mapping key"
    let (v, rv) ← typeName (← field j "valueType")
    return (.mapping k v, .mapping rk rv)
  | _ => throw "compact verifier: unsupported type declaration"

private partial def expression (j : Json) : Except String RawExpr := do
  let kind ← node j
  let type := ((j.getObjVal? "typeDescriptions").toOption.bind fun d => (d.getObjValAs? String "typeString").toOption).getD ""
  if kind != "Literal" && type.isEmpty then throw "missing expression type"
  if constTy j then
    let some n := (constVal j).bind Q.int? | throw "nonintegral compiler constant"
    return if n < 0 then .unop .neg (.num n.natAbs) else .num n.toNat
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
  | "IndexAccess" =>
    let base ← expression (← field j "baseExpression")
    let key ← expression (← field j "indexExpression")
    return .index base key
  | "MemberAccess" => return .field (← expression (← field j "expression")) (← str j "memberName")
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

private def tokens (s : String) : Except String (List String) := do
  let original := specTokens s
  let raw := original.flatMap fun token =>
    if token.contains '.' then String.intercalate " . " (token.splitOn ".") |>.splitOn " " else [token]
  if (original.zip original.tail).any (fun (a,b) =>
      (a == "\\" && b.toList.any Char.isWhitespace) ||
      (a.endsWith "." && b.toList.any Char.isWhitespace) ||
      (a.toList.any Char.isWhitespace && b.startsWith ".") ||
      ["--", "/-", "-/"].contains (a ++ b)) then
    throw "specification whitespace or comment syntax uses the full parser"
  let rec merge : List String → List String
    | a :: b :: rest => if ["==", "!=", "<=", ">=", "&&", "||", "**", "->"].contains (a ++ b)
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
    | "\\" :: "forall" :: ty :: name :: ";" :: rest => do
      let some p := PrimTy.ofName? ty | throw "quantifier type"
      let (body, tail) ← specExpr 1 rest
      return (.all p name body, tail)
    | "!" :: rest => do let (e, rest) ← specExpr 7 rest; return (.unop .not e, rest)
    | "-" :: rest => do let (e, rest) ← specExpr 7 rest; return (.unop .neg e, rest)
    | "true" :: rest => return (.bool true, rest)
    | "false" :: rest => return (.bool false, rest)
    | s :: rest =>
      if let some n := s.toNat? then return (.num n, rest)
      else if !s.isEmpty && s.toList.all (fun c => c.isAlphanum || c == '_' || c == '$') &&
          !(s.toList.head!).isDigit then return (.name s, rest)
      else throw s!"unsupported specification token {s}"
  loop (left : SpecExpr) (ts : List String) (previous : Option Nat) : Except String (SpecExpr × List String) := do
    match ts with
    | "[" :: rest =>
      let (key, tail) ← specExpr 1 rest
      let "]" :: tail := tail | throw "specification index"
      loop (.index left key) tail previous
    | "." :: name :: rest => loop (.field left name) rest previous
    | "->" :: rest =>
      if min > 1 then return (left, ts)
      let (right, tail) ← specExpr 1 rest
      return (.imp left right, tail)
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
    if clause.kind == "box" then continue
    unless clause.kind == "requires" || clause.kind == "ensures" do throw "specification directive"
    let (e, rest) ← specExpr 1 (← tokens clause.text)
    unless rest.isEmpty do throw "unsupported specification suffix"
    if clause.kind == "requires" then out := { out with requires := out.requires ++ [e] }
    else out := { out with ensures := out.ensures ++ [e] }
  return out

private partial def rawSpec : SpecExpr → Except String RawExpr
  | .num n => pure (.num n)
  | .bool b => pure (.bool b)
  | .name n => pure (.name n)
  | .field e f => return .field (← rawSpec e) f
  | .index e k => return .index (← rawSpec e) (← rawSpec k)
  | .binop op a b => return .binop op (← rawSpec a) (← rawSpec b)
  | .unop op a => return .unop op (← rawSpec a)
  | _ => throw "unsupported loop expression"

private partial def rawInvariant : SpecExpr → Except String RawInv
  | .all p n e => return .all p n (← rawInvariant e)
  | .imp a b => return .imp (← rawSpec a) (← rawSpec b)
  | e => return .expr (← rawSpec e)

private def loopSpec (j : Json) : Except String RawLoopSpec := do
  let mut spec : RawLoopSpec := {}
  for annotation in ← arrDefault j "loopSpec" do
    let text ← annotation.getStr?
    let ts ← tokens text
    match ts with
    | "invariant" :: rest =>
      let (e, tail) ← specExpr 1 rest
      unless tail.isEmpty do throw "loop invariant suffix"
      spec := { spec with qinv := spec.qinv ++ [← rawInvariant e] }
    | "decreases" :: rest =>
      if spec.dec.isSome then throw "duplicate loop decreases"
      let (e, tail) ← specExpr 1 rest
      unless tail.isEmpty do throw "loop decreases suffix"
      spec := { spec with dec := some (← rawSpec e) }
    | "unwind" :: [n] =>
      let some bound := n.toNat? | throw "loop unwind bound"
      if spec.unwind.isSome then throw "duplicate loop unwind"
      spec := { spec with unwind := bound }
    | _ => throw "loop annotation"
  return spec

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
    let (t, raw) ← typeName (← field d "typeName")
    let .prim _ := t | throw "reference declaration"
    return [.decl raw (← str d "name") (← (optional j "initialValue").mapM expression)]
  | "WhileStatement" =>
    return [.whileLoop (← loopSpec j) (← expression (← field j "condition")) (← statements (← field j "body"))]
  | "ForStatement" =>
    return [.forLoop (← loopSpec j) ((← (optional j "initializationExpression").mapM statements).getD [])
      (← (optional j "condition").mapM expression)
      ((← (optional j "loopExpression").mapM statements).getD []) (← statements (← field j "body"))]
  | "Break" => return [.brk]
  | "Continue" => return [.cont]
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
      if (← str e "operator") == "delete" then return [.delete (← expression (← field e "subExpression"))]
      let op ← match ← str e "operator" with
        | "++" => pure IncDec.postInc | "--" => pure IncDec.postDec
        | _ => throw "statement unary operator"
      return [.incDec op (← expression (← field e "subExpression"))]
    | "FunctionCall" =>
      let fn ← field e "expression"
      if (← node fn) == "MemberAccess" then
        let name ← str fn "memberName"
        unless name == "push" || name == "pop" do throw "non-builtin member call"
        return [.call (.field (← expression (← field fn "expression")) name)
          (← (← arr e "arguments").toList.mapM expression)]
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
  let mut vars := []
  for n in ← arr j "nodes" do
    match ← node n with
    | "VariableDeclaration" =>
      unless (← str n "mutability") == "mutable" && (optional n "value").isNone do throw "state initializer or constant"
      if (n.getObjValAs? String "storageLocation").toOption == some "transient" then throw "transient storage"
      vars := vars ++ [(← str n "name", (← typeName (← field n "typeName")).1)]
    | "FunctionDefinition" => pure ()
    | _ => throw "contract member"
  if h : vars.all (fun nt => nt.2.okDeep) = true then
    if hn : Semantics.nodupKeysB vars = true then
      return { vars, vars_ok := h, vars_nodup := hn }
    else throw "duplicate storage root"
  else throw "ill-formed storage type"

/-- Plain assertion obligations use the same scoped source elaborator and
box/diamond reading as `solc_scoped_problems`. Everything here is executable;
no Lean expression, declaration or environment is constructed. -/
private def assertionObligation (C : Contract) (name : String) (box : Bool) : Except String (Fml C []) := do
  let some d := Semantics.lookupBy name C.funs | throw "missing function"
  unless d.rets.isEmpty do throw "plain return obligation"
  let ctx ← d.paramCtx
  let (raw, st) ← (lowerBodyLoops [] 0 d.body).runFrom { funs := C.funs }
    (ctx, RawStmt.maxIdxs d.body + 1)
  let raw ← lowerReturns [] raw
  let ⟨_, program⟩ ← (elabProgAtS.go C 0 raw st (source := true)).mapError (·.2)
  let Γ := ECtx.toNCtx st.1
  let m := if box then Modality.box else .diamond
  return Fml.closeN true Γ (.imp (Problem.callPre C Γ false [] false [] true)
    (.imp (Fml.wt C) (.modal m program .nil .tt)))

private structure Stronger {C : Contract} {Γ : Ctx} (φ : Fml C Γ) where
  formula : Fml C Γ
  sound : ∀ σ, holds σ formula → holds σ φ

private def primitivePositions {Γ : Ctx} : (xs : List ((t : LTy) × Idx Γ t)) →
    Option ((ps : AnonLocalCapture.Positions Γ) ×' AnonLocalCapture.keys ps = xs)
  | [] => some ⟨[], rfl⟩
  | ⟨.val p, j⟩ :: xs => do
    let ⟨ps, h⟩ ← primitivePositions xs
    return ⟨⟨p, j⟩ :: ps, congrArg (@List.cons ((t : LTy) × Idx Γ t) ⟨.val p, j⟩) h⟩
  | _ => none

/-- A sound compiled version of the existing anonymous-local leaf preparation.
The copied positions stay intrinsic; its proof is erased from the executable. -/
private def prepareLeaf {C : Contract} : Nat → {Γ : Ctx} → (φ : Fml C Γ) → Stronger φ
  | 0, _, φ => ⟨φ, fun _ h => h⟩
  | n+1, _, .imp a b =>
    let r := prepareLeaf n b
    let skipPremise := match a with | .wellFormed _ => true | _ => false
    if skipPremise then ⟨r.formula, fun σ h _ => r.sound σ h⟩
    else ⟨.imp a r.formula, fun σ h ha => r.sound σ (h ha)⟩
  | n+1, _, .and a b =>
    let ra := prepareLeaf n a
    let rb := prepareLeaf n b
    ⟨.and ra.formula rb.formula, fun σ h => ⟨ra.sound σ h.1, rb.sound σ h.2⟩⟩
  | n+1, _, .upd m U b =>
    let r := prepareLeaf n b
    ⟨.upd m U r.formula, fun _ h => Upd.afterT_imp h (fun τ hτ => r.sound τ hτ)⟩
  | n+1, _, .all x p b =>
    let r := prepareLeaf n b
    ⟨.all x p r.formula, fun σ h v => r.sound (σ.push v) (h v)⟩
  | n+1, _, .bind _ x (.val p) b =>
    let r := prepareLeaf n b
    ⟨.all x p r.formula, fun σ h v => r.sound (σ.push v) (h v)⟩
  | n+1, _, .bind m x t b =>
    let r := prepareLeaf n b
    ⟨.bind m x t r.formula, fun σ h => Modality.forallB_imp (fun v hv => r.sound (σ.push v) hv) h⟩
  | n+1, _, .anon xs b =>
    match primitivePositions xs with
    | none => ⟨.anon xs b, fun _ h => h⟩
    | some ⟨ps, he⟩ =>
      let r := prepareLeaf n b
      let names := Var.fresh "directAnon"
      let k := max r.formula.maxIdx C.rootMaxIdx + 1
      let plan := prepareLeaf n (AnonLocalCapture.plan .box names k ps r.formula)
      ⟨plan.formula, fun σ h =>
        Eq.mp (congrArg (fun keys => holds σ (.anon keys b)) he)
          (fun values => r.sound (σ.anon (AnonLocalCapture.keys ps) values)
            (AnonLocalCapture.sound .box names k ps r.formula σ (plan.sound σ h) values))⟩
  | _+1, _, φ => ⟨φ, fun _ h => h⟩

/-- Apply the compiled arithmetic decision procedure to each symbolic leaf,
including the preservation/exit leaves produced by loop invariants. Applying
it only to the original modal formula misses these ordinary arithmetic goals. -/
private def arithmeticLeaf {C : Contract} {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List (Seq.SLeaf C)) :=
  match SpecProposal.leaf H φ with
  | some [] => some []
  | result => if (H.wrap φ).modalFree && Tools.directArithmetic (prepareLeaf 512 (H.wrap φ)).formula
      then some [] else result

private def compiledResult (C : Contract) (φ : Fml C []) : Json :=
  if !(Fml.callsBack false φ) &&
      ((Seq.run .all arithmeticLeaf Seq.refuteLanded 1024 .nil φ 1024).map (·.1)).any List.isEmpty then
    Json.mkObj [("status", toJson "proved"), ("reason", toJson "")]
  else Solidity.Frontend.directResult C φ

private partial def hasAnnotatedLoop (ss : List RawStmt) : Bool :=
  ss.any fun s =>
    let annotated := match s with
      | .whileLoop a .. | .forLoop a .. | .doWhile a .. | .loop a .. =>
        !a.inv.isEmpty || !a.qinv.isEmpty || a.dec.isSome || a.unwind.isSome
      | _ => false
    annotated || s.blocks.any hasAnnotatedLoop

/-- Annotations choose proof rules; they do not change loop execution
(`Stmt.run_loop`). A bounded exact-unrolling retry can therefore close short
loops whose quantified invariant lies outside the executable leaf fragment. -/
private partial def unrollLoops (ss : List RawStmt) : List RawStmt :=
  ss.map fun s => match s.mapBlocks unrollLoops with
    | .whileLoop _ c b => .whileLoop {} c b
    | .forLoop _ i c u b => .forLoop {} i c u b
    | .doWhile _ b c => .doWhile {} b c
    | .loop _ c b => .loop {} c b
    | s => s

/-- No parser, elaborator environment, proof term or module file is loaded.
The same intrinsic obligation builder and executable verifier are called. -/
def check (request : Json) : Except String Json := do
  let source ← field request "contract"
  let base ← contract source
  let avoid := source.compress
  let selected := (request.getObjValAs? String "function").toOption
  let selectedId := (request.getObjValAs? Int "sourceId").toOption
  let listing := (request.getObjValAs? Bool "listing").toOption.getD false
  let mut rows := #[]
  for n in ← arr source "nodes" do
    unless (← node n) == "FunctionDefinition" do continue
    let name ← str n "name"
    if selected.isSome && selected != some name then continue
    if selectedId.isSome && selectedId != (n.getObjValAs? Int "id").toOption then continue
    let visibility ← str n "visibility"
    unless visibility == "public" || visibility == "external" do continue
    let clauses ← keyClauses (docText n)
    let specified := clauses.any (fun c => c.kind == "requires" || c.kind == "ensures")
    let result : Json := if clauses.any (·.kind == "skip") then
        Json.mkObj [("status", toJson "skipped"), ("reason", toJson "tagged `@custom:key skip`")]
      else match (do
        let (_, d) ← function n avoid
        let C := { base with funs := [(name, d)] }
        let φ ← if specified then specObligation C name
          else assertionObligation C name (clauses.any (·.kind == "box"))
        if listing then return Json.mkObj [("status", toJson "ready"), ("reason", toJson "")]
        let result := compiledResult C φ
        if (result.getObjValAs? String "status").toOption == some "pending" && hasAnnotatedLoop d.body then
          let d := { d with body := unrollLoops d.body }
          let C := { base with funs := [(name, d)] }
          let φ ← if specified then specObligation C name
            else assertionObligation C name (clauses.any (·.kind == "box"))
          return compiledResult C φ
        return result) with
      | .ok result => result
      | .error reason => Json.mkObj [("status", toJson "unsupported"), ("reason", toJson reason)]
    let result := match result.getObjVal? "counterexample" with
      | .error _ => result
      | .ok witness => match witness.getObjValAs? (Array Json) "arguments" with
        | .error _ => result
        | .ok args =>
          let args := args.map fun (arg : Json) =>
            match arg.getObjValAs? String "modelName" with
            | .error _ => arg
            | .ok name => match ((J.arrD (J.opt n "parameters" |>.getD .null) "parameters").toList).findIdx?
                (fun p => J.str? p "name" == some name) with
              | none => arg
              | some i => arg.setObjVal! "paramIndex" (toJson i)
          result.setObjVal! "counterexample" (witness.setObjVal! "arguments" (toJson args))
    let result := result.setObjVal! "function" (toJson name)
      |>.setObjVal! "sourceId" (← field n "id")
      |>.setObjVal! "verification" (toJson "direct")
      |>.setObjVal! "reading" (toJson "solc")
      |>.setObjVal! "tag" (toJson (if specified then "specified" else
        if ((keyClauses (docText n)).toOption.getD []).any (·.kind == "box") then "box" else "diamond"))
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
