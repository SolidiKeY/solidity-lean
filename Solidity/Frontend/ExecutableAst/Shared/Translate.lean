import Solidity.Frontend.ExecutableAst.Shared.Boundary
import Solidity.Frontend.SolcJson.Contract

/-! # Existing executable AST translation

Extracted from Tools.DirectRuntime at the frozen dispatch base. Recursive
one-step functions accept explicit readers for owned extension modules.
H90 adds primitive narrow locals with their source spelling; parameter/state
readers and unrelated refusal paths retain the original fragment/errors.
This module depends on neither Frontend.Import nor Frontend.Testing.
Producer migration and parity are separate required gates.
-/
namespace Solidity.Frontend.ExecutableAst.Shared
open Lean Solidity.Frontend

def field (j : Json) (s : String) : Except String Json := j.getObjVal? s
def str (j : Json) (s : String) : Except String String := j.getObjValAs? String s
def arr (j : Json) (s : String) : Except String (Array Json) := j.getObjValAs? (Array Json) s
def arrDefault (j : Json) (s : String) : Except String (Array Json) :=
  match j.getObjVal? s with | .error _ => pure #[] | .ok v => v.getArr?
def node (j : Json) : Except String String := str j "nodeType"
def optional (j : Json) (s : String) : Option Json :=
  match j.getObjVal? s with | .ok .null => none | .ok v => some v | _ => none
def prim (j : Json) : Except String Ty := do
  let t ← str (← field j "typeDescriptions") "typeString"
  match t with
  | "uint256" => return .prim .uint
  | "int256" => return .prim .int
  | "bool" => return .prim .bool
  | _ => throw s!"compact verifier: unsupported type {t}"

/-- Shape gate for primitive expression leaves in local tuples. Width semantics
remain with each declaration's retained RawTy spelling and existing elaboration.
Parameter decoding deliberately keeps `prim`, since Ty alone erases width. -/
def localPrim (j : Json) : Except String Ty := do
  let spelling ← str (← field j "typeDescriptions") "typeString"
  if let some (p, _) := narrowTy? spelling then return .prim p
  if (bytesTy? spelling).isSome || spelling == "address" then return .prim .uint
  prim j

def typeNameStep (read : Json → Except String (Ty × RawTy)) (j : Json) : Except String (Ty × RawTy) := do
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
    let (t, raw) ← read (← field j "baseType")
    if let some len := optional j "length" then
      let some n := (constVal len).bind Q.int? | throw "array length"
      unless n ≥ 0 do throw "negative array length"
      return (.fixed t n.toNat, .fixed raw n.toNat)
    return (.array t, .array raw)
  | "Mapping" =>
    let (.prim k, rk) ← read (← field j "keyType") | throw "mapping key"
    let (v, rv) ← read (← field j "valueType")
    return (.mapping k v, .mapping rk rv)
  | _ => throw "compact verifier: unsupported type declaration"

partial def typeName (j : Json) : Except String (Ty × RawTy) :=
  typeNameStep typeName j

/-- A primitive local retains its source narrow spelling for the existing
width-aware declaration elaborator. Parameters and state roots still use their
original readers: returning only `Ty` there would discard width metadata. -/
def localTypeName (j : Json) : Except String (Ty × RawTy) :=
  match node j with
  | .error e => .error e
  | .ok kind =>
    if kind == "ElementaryTypeName" then
      match str j "name" with
      | .error e => .error e
      | .ok name =>
        match narrowTy? name with
        | some (p, _) => .ok (.prim p, .named name)
        | none =>
          match bytesTy? name with
          | some _ => .ok (.prim .uint, .named name)
          | none => typeName j
    else typeName j

/-- Every canonical narrow local keeps its exact spelling; this is a decoder
fact, not an adequacy theorem for compiler expressions or intrinsic programs. -/
theorem localTypeName_of_narrow (j : Json) (name : String) (p : PrimTy) (width : Nat)
    (hkind : node j = .ok "ElementaryTypeName") (hname : str j "name" = .ok name)
    (hwidth : narrowTy? name = some (p, width)) :
    localTypeName j = .ok (.prim p, .named name) := by
  simp only [localTypeName, hkind, beq_self_eq_true, ↓reduceIte, hname, hwidth]

/-- Canonical fixed-byte locals retain their exact marker-bearing spelling.
This general decoder fact is not an AST/source or intrinsic adequacy theorem. -/
theorem localTypeName_of_fixedBytes (j : Json) (name : String) (size : Nat)
    (hkind : node j = .ok "ElementaryTypeName") (hname : str j "name" = .ok name)
    (hnarrow : narrowTy? name = none) (hbytes : bytesTy? name = some size) :
    localTypeName j = .ok (.prim .uint, .named name) := by
  simp only [localTypeName, hkind, beq_self_eq_true, ↓reduceIte, hname, hnarrow, hbytes]

/-- One local-type dispatch: explicitly nonpayable addresses retain their marker;
other shapes use the existing narrow/fixed-byte local reader. This is a shape
choice, not retrying a failed translation. Missing/payable metadata stays refused. -/
def localValueTypeName (j : Json) : Except String (Ty × RawTy) :=
  if (node j).toOption == some "ElementaryTypeName" &&
      (str j "name").toOption == some "address" then
    if (str j "stateMutability").toOption == some "nonpayable" then
      .ok (.prim .uint, .named "address")
    else typeName j
  else localTypeName j

/-- Explicit nonpayable address metadata retains its exact marker-bearing spelling.
This general decoder equation is not a source/ABI adequacy theorem. -/
theorem localValueTypeName_of_address (j : Json)
    (hkind : node j = .ok "ElementaryTypeName") (hname : str j "name" = .ok "address")
    (hmut : str j "stateMutability" = .ok "nonpayable") :
    localValueTypeName j = .ok (.prim .uint, .named "address") := by
  simp only [localValueTypeName, hkind, hname, hmut, Except.toOption,
    beq_self_eq_true, Bool.and_self, ↓reduceIte]

/-- Guards existing environment reads against ordinary member/name confusion.
Only compiler magic roots with negative builtin identity and the expected result
spelling use the existing EnvKey map. Other members stay on the field path.
This metadata decoder is not a source/environment adequacy certificate. -/
def environmentMember? (base : Json) (member resultType : String) : Option EnvKey := do
  if (node base).toOption != some "Identifier" then none else do
  let root ← (str base "name").toOption
  let key ← EnvKey.ofParts root member
  let expectedMagic ← match root with
    | "msg" => some "t_magic_message"
    | "block" => some "t_magic_block"
    | _ => none
  let metadata ← (field base "typeDescriptions").toOption
  if (str metadata "typeIdentifier").toOption != some expectedMagic then none else do
  if !(J.ref? base).any (· < 0) then none else do
  let expectedType := match key with | .msgSender => "address" | _ => "uint256"
  if resultType != expectedType then none else some key

/-- One shared inversion of every successful environment decode: existing map
entry, negative builtin reference and selected result spelling. This guards
metadata/type confusion, not compiler identity or source/world adequacy. -/
theorem environmentMember?_guards (base : Json) (member resultType : String)
    (key : EnvKey) (success : environmentMember? base member resultType = some key) :
    (∃ root : String, (str base "name").toOption = some root ∧
      EnvKey.ofParts root member = some key) ∧ (J.ref? base).any (· < 0) = true ∧
      resultType = (fun selected : EnvKey =>
        match selected with | .msgSender => "address" | _ => "uint256") key := by
  unfold environmentMember? at success
  split at success
  next => cases success
  next =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at success
    rcases success with ⟨root, hroot, mapped, hmap, success⟩
    split at success <;>
      simp only [Option.bind_some, Option.bind_none, Option.bind_eq_some_iff] at success
    all_goals try contradiction
    all_goals
      rcases success with ⟨metadata, hmetadata, success⟩
      split at success
      next => cases success
      next =>
        split at success
        next => cases success
        next notnegative =>
          let expectedType : EnvKey → String := fun selected =>
            match selected with | .msgSender => "address" | _ => "uint256"
          by_cases hresult : (resultType != expectedType mapped) = true
          · rw [if_pos hresult] at success
            cases success
          · rw [if_neg hresult] at success
            have same : mapped = key := Option.some.inj success
            subst mapped
            have validType : resultType = expectedType key := by
              simpa only [bne_iff_ne, Decidable.not_not] using hresult
            refine ⟨⟨_, hroot, hmap⟩, ?_, validType⟩
            cases hn : (J.ref? base).any (· < 0) with
            | false => exact False.elim (notnegative (by rw [hn]; rfl))
            | true => rfl

/-- A successful environment decoder selects an existing EnvKey map entry and
has a negative builtin reference. This general guard inversion is not compiler
identity authentication or a source/world adequacy theorem. -/
theorem environmentMember?_guard (base : Json) (member resultType : String)
    (key : EnvKey) (success : environmentMember? base member resultType = some key) :
    (∃ root : String, (str base "name").toOption = some root ∧
      EnvKey.ofParts root member = some key) ∧ (J.ref? base).any (· < 0) = true := by
  let guards := environmentMember?_guards base member resultType key success
  exact ⟨guards.1, guards.2.1⟩

/-- All explicit builtin metadata guards suffice for the existing decoder. This
construction theorem guards accidental refusal of valid metadata; it does not
authenticate compiler identities or establish source/world adequacy. -/
theorem environmentMember?_of_metadata (base metadata : Json)
    (root member magic resultType : String) (key : EnvKey)
    (hkind : (node base).toOption = some "Identifier")
    (hroot : (str base "name").toOption = some root)
    (hkey : EnvKey.ofParts root member = some key)
    (hmagic : (fun name : String => match name with
      | "msg" => some "t_magic_message"
      | "block" => some "t_magic_block"
      | _ => none) root = some magic)
    (hmetadata : (field base "typeDescriptions").toOption = some metadata)
    (hidentifier : (str metadata "typeIdentifier").toOption = some magic)
    (href : (J.ref? base).any (· < 0) = true)
    (htype : resultType = (fun selected : EnvKey =>
      match selected with | .msgSender => "address" | _ => "uint256") key) :
    environmentMember? base member resultType = some key := by
  dsimp only at hmagic
  split at hmagic <;> simp only [Option.some.injEq, reduceCtorEq] at hmagic
  all_goals try contradiction
  all_goals subst magic
  all_goals
    simp only [environmentMember?, hkind, hroot, hkey, hmetadata, hidentifier,
      href, htype, Option.bind_eq_bind, Option.bind_some, bne_self_eq_false,
      Bool.false_eq_true, Bool.not_true, ↓reduceIte]

/-- Successful environment decoding enforces the selected key's result type.
This invariant guards metadata/result-type confusion for arbitrary JSON inputs;
it is not a compiler type-soundness or source/world adequacy theorem. -/
theorem environmentMember?_resultType (base : Json) (member resultType : String)
    (key : EnvKey) (success : environmentMember? base member resultType = some key) :
    resultType = (fun selected : EnvKey =>
      match selected with | .msgSender => "address" | _ => "uint256") key := by
  exact (environmentMember?_guards base member resultType key success).2.2

def expressionStep (read : Json → Except String RawExpr) (j : Json) : Except String RawExpr := do
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
    let base ← read (← field j "baseExpression")
    let key ← read (← field j "indexExpression")
    return .index base key
  | "MemberAccess" =>
    let base ← field j "expression"
    let decoded ← read base
    let member ← str j "memberName"
    if let some key := environmentMember? base member type then return .env key
    return .field decoded member
  | "BinaryOperation" =>
    let some op := BinOp.ofSym? (← str j "operator") | throw "binary operator"
    return .binop op (← read (← field j "leftExpression")) (← read (← field j "rightExpression"))
  | "UnaryOperation" =>
    let op ← match ← str j "operator" with
      | "-" => pure UnOp.neg | "!" => pure UnOp.not | "~" => pure UnOp.bnot
      | _ => throw "unary operator"
    return .unop op (← read (← field j "subExpression"))
  | "Conditional" =>
    let c ← read (← field j "condition")
    let a ← read (← field j "trueExpression")
    let b ← read (← field j "falseExpression")
    return .ternary c a b
  | _ => throw "compact verifier: unsupported expression"

partial def expression (j : Json) : Except String RawExpr :=
  expressionStep expression j

def tokens (s : String) : Except String (List String) := do
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

def precedence : String → Nat
  | "||" => 1 | "&&" => 2 | "==" | "!=" => 3
  | "<" | ">" | "<=" | ">=" => 4
  | "+" | "-" => 5 | "*" | "/" | "%" => 6 | _ => 0

partial def specExpr (min : Nat) (ts : List String) : Except String (SpecExpr × List String) := do
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

def specification (j : Json) : Except String FunSpec := do
  let mut out : FunSpec := {}
  for clause in ← keyClauses (docText j) do
    if clause.kind == "box" then continue
    unless clause.kind == "requires" || clause.kind == "ensures" do throw "specification directive"
    let (e, rest) ← specExpr 1 (← tokens clause.text)
    unless rest.isEmpty do throw "unsupported specification suffix"
    if clause.kind == "requires" then out := { out with requires := out.requires ++ [e] }
    else out := { out with ensures := out.ensures ++ [e] }
  return out

partial def rawSpec : SpecExpr → Except String RawExpr
  | .num n => pure (.num n)
  | .bool b => pure (.bool b)
  | .name n => pure (.name n)
  | .field e f => return .field (← rawSpec e) f
  | .index e k => return .index (← rawSpec e) (← rawSpec k)
  | .binop op a b => return .binop op (← rawSpec a) (← rawSpec b)
  | .unop op a => return .unop op (← rawSpec a)
  | _ => throw "unsupported loop expression"

partial def rawInvariant : SpecExpr → Except String RawInv
  | .all p n e => return .all p n (← rawInvariant e)
  | .imp a b => return .imp (← rawSpec a) (← rawSpec b)
  | e => return .expr (← rawSpec e)

def loopSpec (j : Json) : Except String RawLoopSpec := do
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

def statementsStep
    (readExpr : Json → Except String RawExpr)
    (readStmts : Json → Except String (List RawStmt))
    (readType : Json → Except String (Ty × RawTy)) (j : Json) : Except String (List RawStmt) := do
  match ← node j with
  | "Block" => return [.block (← (← arr j "statements").toList.mapM readStmts).flatten]
  | "UncheckedBlock" =>
    let body ← (← arr j "statements").toList.mapM readStmts
    return [.block [.unchecked body.flatten]]
  | "Return" => return [.ret (← (optional j "expression").mapM readExpr)]
  | "IfStatement" => return [.ite (← readExpr (← field j "condition"))
      (← readStmts (← field j "trueBody")) (← match optional j "falseBody" with
        | none => pure [] | some e => readStmts e)]
  | "VariableDeclarationStatement" =>
    let ds ← arr j "declarations"
    unless ds.size == 1 do throw "tuple declaration"
    let d := ds[0]!
    let (t, raw) ← readType (← field d "typeName")
    let .prim _ := t | throw "reference declaration"
    return [.decl raw (← str d "name") (← (optional j "initialValue").mapM readExpr)]
  | "WhileStatement" =>
    return [.whileLoop (← loopSpec j) (← readExpr (← field j "condition")) (← readStmts (← field j "body"))]
  | "ForStatement" =>
    return [.forLoop (← loopSpec j) ((← (optional j "initializationExpression").mapM readStmts).getD [])
      (← (optional j "condition").mapM readExpr)
      ((← (optional j "loopExpression").mapM readStmts).getD []) (← readStmts (← field j "body"))]
  | "Break" => return [.brk]
  | "Continue" => return [.cont]
  | "ExpressionStatement" =>
    let e ← field j "expression"
    match ← node e with
    | "Assignment" =>
      let l ← readExpr (← field e "leftHandSide")
      let r ← readExpr (← field e "rightHandSide")
      match ← str e "operator" with
      | "=" => return [.assign l r]
      | op =>
        let some b := BinOp.ofSym? (op.take (op.length - 1)) | throw "assignment operator"
        unless op.endsWith "=" && b.hasCompoundAssign do throw "assignment operator"
        return [.opAssign b l r]
    | "UnaryOperation" =>
      if (← str e "operator") == "delete" then return [.delete (← readExpr (← field e "subExpression"))]
      let op ← match ← str e "operator" with
        | "++" => pure IncDec.postInc | "--" => pure IncDec.postDec
        | _ => throw "statement unary operator"
      return [.incDec op (← readExpr (← field e "subExpression"))]
    | "FunctionCall" =>
      let fn ← field e "expression"
      if (← node fn) == "MemberAccess" then
        let name ← str fn "memberName"
        unless name == "push" || name == "pop" do throw "non-builtin member call"
        return [.call (.field (← readExpr (← field fn "expression")) name)
          (← (← arr e "arguments").toList.mapM readExpr)]
      unless (← node fn) == "Identifier" do throw "call receiver"
      let name ← str fn "name"
      let some identity := (fn.getObjValAs? Int "referencedDeclaration").toOption
        | throw "missing builtin declaration identity"
      unless identity < 0 && (name == "assert" || name == "require") do
        throw "non-builtin call"
      let args ← arr e "arguments"
      unless args.size == 1 do throw "call arguments"
      let condition ← readExpr args[0]!
      match ← str fn "name" with
      | "assert" => return [.assert condition]
      | "require" => return [.require condition]
      | _ => throw "function call"
    | _ => throw "expression statement"
  | _ => throw "compact verifier: unsupported statement"


partial def statements (j : Json) : Except String (List RawStmt) :=
  statementsStep expression statements localValueTypeName j

def params (j : Json) (returns : Bool) (fresh : String) : Except String (List (String × Ty)) := do
  (← arr j "parameters").toList.zipIdx.mapM fun (p, i) => do
    let n ← str p "name"
    if n.isEmpty && !returns then throw "unnamed parameter"
    return (if n.isEmpty then s!"{fresh}{i}" else n, ← prim p)

/-- Existing executable readers. Extensions capture resolved declaration tables
in these functions and route recursive children through the one-step APIs.
An error is final; it is never a signal to retry another translation path. -/
def reader : Reader := { typeName, expression, statements, params, specification }

private def decodeFunction (read : Reader) (j : Json) (avoid : String) : Except String (String × FunDecl) := do
  unless (← str j "kind") == "function" && (← arrDefault j "modifiers").isEmpty do throw "constructor or modifiers"
  let spec ← read.specification j
  let mut fresh := "__solidity_direct_return_"
  while (avoid.splitOn fresh).length > 1 do fresh := fresh ++ "_"
  let ps ← read.params (← field j "parameters") false fresh
  let rs ← read.params (← field j "returnParameters") true fresh
  let rawBody ← field j "body"
  unless (← node rawBody) == "Block" do throw "function body"
  let body := (← (← arr rawBody "statements").toList.mapM read.statements).flatten
  let payable := (← str j "stateMutability") == "payable"
  return (← str j "name", { params := ps, rets := rs, body, spec, payable })

private def decodeContract (read : Reader) (j : Json) : Except String Contract := do
  unless (← str j "contractKind") == "contract" && (← arrDefault j "baseContracts").isEmpty do throw "inheritance or interface"
  unless (← keyClauses (docText j)).isEmpty do throw "contract specification"
  let mut vars := []
  for n in ← arr j "nodes" do
    match ← node n with
    | "VariableDeclaration" =>
      unless (← str n "mutability") == "mutable" && (optional n "value").isNone do throw "state initializer or constant"
      if (n.getObjValAs? String "storageLocation").toOption == some "transient" then throw "transient storage"
      vars := vars ++ [(← str n "name", (← read.typeName (← field n "typeName")).1)]
    | "FunctionDefinition" => pure ()
    | _ => throw "contract member"
  if h : vars.all (fun nt => nt.2.okDeep) = true then
    if hn : Semantics.nodupKeysB vars = true then
      return { vars, vars_ok := h, vars_nodup := hn }
    else throw "duplicate storage root"
  else throw "ill-formed storage type"

/-- Metadata-only validation after a complete legacy root has decoded.
The existing J.nodes walker also visits constant-folded children. This pass
constructs no Raw syntax, term, program, formula, or alternate translator. -/
def validateMetadata (j : Json) : Except String Unit := do
  for n in J.nodes j do
    if ["Identifier", "Literal", "UnaryOperation", "BinaryOperation", "Conditional",
        "Assignment", "IndexAccess", "MemberAccess", "FunctionCall", "NewExpression",
        "IndexRangeAccess", "TupleExpression"].contains (J.kind n) && (J.tyStr n).isEmpty then
      throw "expression lacks its compiler type"
    if J.kind n == "UnaryOperation" && !(n.getObjValAs? Bool "prefix").isOk then
      throw "unary expression lacks its prefix flag"
    if J.kind n == "BinaryOperation" &&
        ((J.opt n "commonType").bind (J.str? · "typeString")).all (·.isEmpty) then
      throw "binary expression lacks its common type"
    if J.kind n == "Literal" && J.str? n "kind" == some "bool" then
      let value ← str n "value"
      unless value == "true" || value == "false" do throw "a malformed boolean literal"
    if J.hasOperatorFunction n then
      let some id := J.operatorFunction? n |
        throw "a malformed resolved operator function annotation"
      unless id > 0 do throw "an operator alias must name a positive declaration identity"
      throw "compact verifier: unsupported operator alias"

/-- Standalone expression admission: one legacy decode, then metadata checks.
A legacy refusal is returned before any new metadata refusal is considered. -/
def checkedExpression (j : Json) : Except String RawExpr := do
  let result ← expression j
  validateMetadata j
  return result

/-- Standalone statement-root admission with the same two-phase ordering. -/
def checkedStatements (j : Json) : Except String (List RawStmt) := do
  let result ← statements j
  validateMetadata j
  return result

/-- The public function boundary validates only after the entire legacy decode.
Raw Reader callbacks remain decoding inputs; they do not certify admission. -/
def function (read : Reader) (j : Json) (avoid : String) : Except String (String × FunDecl) := do
  let result ← decodeFunction read j avoid
  unless J.kind j == "FunctionDefinition" do throw "compact verifier: expected function definition"
  validateMetadata j
  return result

/-- Validate admitted storage metadata without inspecting sibling function bodies.
The original whole-contract refusal retains priority over new metadata checks. -/
def contract (read : Reader) (j : Json) : Except String Contract := do
  let result ← decodeContract read j
  unless J.kind j == "ContractDefinition" do throw "compact verifier: expected contract definition"
  for member in ← arr j "nodes" do
    if (← node member) == "VariableDeclaration" then validateMetadata member
  return result

end Solidity.Frontend.ExecutableAst.Shared
