import Lean.Data.Json
import Solidity.Frontend.Checked.Parser
import Solidity.Frontend.Checked.Prec
import Solidity.Frontend.Checked.Lexer
import Solidity.Yul.ExpressionCheck

/-! Pinned solc JSON expression ingress. This reuses G08's numeric/identifier/hex
recognizers and S00 tree, not a second lexer or an untyped intermediate AST.
It does not admit a whole assembly block or certify its metadata/environment. -/
namespace Solidity.Frontend.YulJson
open Lean (Json)
open Solidity.Source (Syn YulLit)
open Solidity.Frontend.Checked
open Solidity.Yul

inductive Error where
  | json (message : String)
  | field (name : String)
  | node (actual : String)
  | identifier (name : String)
  | annotation (name : String)
  | literal (kind : String)
  | literalRange
  | depth
  | shape
  | staticExpression
  deriving Repr, DecidableEq

def field (j : Json) (key : String) : Except Error Json :=
  (j.getObjVal? key).mapError (fun _ => .field key)

def string (j : Json) (key : String) : Except Error String :=
  (j.getObjValAs? String key).mapError (fun _ => .field key)

def array (j : Json) (key : String) : Except Error (Array Json) := do
  ((← field j key).getArr?).mapError (fun _ => .field key)

def bytes (s : String) : Solidity.Frontend.Checked.Bytes := s.toUTF8.data.toList

def requireNode (j : Json) (expected : String) : Except Error Unit := do
  let actual ← string j "nodeType"
  if actual = expected then pure () else throw (.node actual)

def emptyAnnotation (j : Json) : Except Error Unit := do
  let t ← string j "type"
  if t.isEmpty then pure () else throw (.annotation t)

/-- A literal arrives with its intrinsic word and independent literal derivation. -/
structure Literal where
  tree : YulLit
  value : Word
  derivation : LiteralD tree value

def finishLiteral (l : YulLit) : Except Error Literal :=
  match inferLiteral l with
  | none => .error .literalRange
  | some ⟨w, d⟩ => .ok ⟨l, w, d⟩

/-- JSON string forms are canonicalized to the existing hex-string grammar
constructor. The decoded bytes and left-aligned word meaning are unchanged;
JSON does not preserve whether the source used quoted or hex-string spelling. -/
def literal (j : Json) : Except Error Literal := do
  requireNode j "YulLiteral"
  emptyAnnotation j
  let kind ← string j "kind"
  if kind = "number" then
    let value ← string j "value"
    match yulNumber (bytes value) with
    | some (.yulDec n) => finishLiteral (.dec n)
    | some (.yulHex n) => finishLiteral (.hex n)
    | _ => throw (.literal kind)
  else if kind = "bool" then
    let value ← string j "value"
    if value = "true" then finishLiteral (.bool true)
    else if value = "false" then finishLiteral (.bool false)
    else throw (.literal kind)
  else if kind = "string" then
    let value ← string j "hexValue"
    let raw := bytes value
    if !raw.all isHexDigit then throw (.literal kind)
    match hexBody raw with
    | some bs => finishLiteral (.hexStr bs)
    | none => throw (.literal kind)
  else throw (.literal kind)

/-- Each path component must be an identifier recognized by the existing Yul
lexer. Keywords/empty components are not silently turned into names. -/
def identifierPath (j : Json) : Except Error (String × List String) := do
  requireNode j "YulIdentifier"
  let name ← string j "name"
  let parts := name.splitOn "."
  if !(parts.all fun part => match yulTok (bytes part) with
      | some (.ident actual) => actual == part
      | _ => false) then throw (.identifier name)
  match parts with
  | head :: tail => pure (head, tail)
  | [] => throw (.identifier name)

def functionName (j : Json) : Except Error String := do
  let (head, tail) ← identifierPath j
  if tail.isEmpty then pure head else throw (.identifier (externalKey head tail))

/-- The recursion argument decreases only at a JSON expression child. The
raw-text wrapper derives its bound from input bytes, not a fixed parser budget. -/
def expressionAux : Nat → Json → Except Error (Syn .yulExpr)
  | 0, _ => .error .depth
  | n + 1, j => do
    let kind ← string j "nodeType"
    if kind = "YulLiteral" then
      pure (.yulLit (← literal j).tree)
    else if kind = "YulIdentifier" then
      let (head, tail) ← identifierPath j
      pure (.yulPath head tail)
    else if kind = "YulFunctionCall" then
      let name ← functionName (← field j "functionName")
      let args ← ((← array j "arguments").toList).mapM (expressionAux n)
      pure (.yulCall name (toSynList args))
    else throw (.node kind)

def expression (bound : Nat) (j : Json) : Except Error (Syn .yulExpr) := expressionAux bound j

/-- A checked ingress result retains its exact parse and intrinsic static proof.
The caller still supplies the declaration/local/function environment. -/
structure CheckedExpression {F X n} (E : ExprEnv F X n) (bound : Nat) (j : Json) where
  tree : Syn .yulExpr
  arity : Nat
  parsed : expression bound j = .ok tree
  derivation : ExprD E tree arity

def checkExpression {F X n} (E : ExprEnv F X n) (bound : Nat) (j : Json) : Except Error (CheckedExpression E bound j) :=
  match hp : expression bound j with
  | .error e => .error e
  | .ok tree => match inferExpr E tree with
    | none => .error .staticExpression
    | some ⟨arity, derivation⟩ => .ok ⟨tree, arity, hp, derivation⟩

def CheckedExpression.term {F X n E bound j} (e : @CheckedExpression F X n E bound j) : Expr F X n e.arity :=
  e.derivation.term

/-- This is an exact parse/static contract for supplied tables, not whole-block
admission or a source/compiler execution correspondence theorem. -/
theorem CheckedExpression.contract {F X n E bound j} (e : @CheckedExpression F X n E bound j) :
    expression bound j = .ok e.tree ∧ Nonempty (ExprD E e.tree e.arity) :=
  ⟨e.parsed, ⟨e.derivation⟩⟩

/-- At the raw-text boundary the traversal bound comes from actual input
bytes. No fixed nesting budget is enlarged. Sufficiency/completeness of this
JSON-to-grammar adapter is a separate obligation; success carries static proof. -/
def checkExpressionText {F X n} (E : ExprEnv F X n) (raw : String) :
    Except Error ((j : Json) × CheckedExpression E (raw.toUTF8.size + 1) j) := do
  let j ← (Json.parse raw).mapError Error.json
  let checked ← checkExpression E (raw.toUTF8.size + 1) j
  pure ⟨j, checked⟩


/-- Parameter/declaration names have no suffix and no type annotation in
Solidity inline assembly. This checks spelling, not freshness or visibility. -/
def typedName (j : Json) : Except Error String := do
  requireNode j "YulTypedName"
  emptyAnnotation j
  let name ← string j "name"
  match yulTok (bytes name) with
  | some (.ident actual) =>
    if actual = name then pure name else throw (.identifier name)
  | _ => throw (.identifier name)

def names (j : Json) (key : String) : Except Error (List String) :=
  do ((← array j key).toList).mapM typedName

/-- The pinned exporter omits empty function parameter/result arrays.
A present malformed field is still an error. -/
def optionalNames (j : Json) (key : String) : Except Error (List String) :=
  match j.getObjVal? key with
  | .error _ => pure []
  | .ok _ => names j key

/-- A structurally smaller decoder handles bodies. Cases are compared by
decoded word: true and 1 cannot evade the duplicate test. Default is last and
unique. This does not check selector or body typing. -/
def switchCases (body : Json → Except Error (Syn (.list .yulStmt))) :
    List Json → List Word → Except Error
      (Syn (.list .yulCase) × Syn (.opt (.list .yulStmt)))
  | [], _ => pure (.nil, .none)
  | j :: rest, seen => do
    requireNode j "YulCase"
    let value ← field j "value"
    match value with
    | .str "default" =>
      if !rest.isEmpty then throw (.node "default must be last")
      pure (.nil, .some (← body (← field j "body")))
    | _ =>
      let l ← literal value
      if seen.contains l.value then throw (.node "duplicate case word")
      let b ← body (← field j "body")
      let (cases, fallback) ← switchCases body rest (l.value :: seen)
      pure (.cons (.yulCase l.tree b) cases, fallback)

mutual
  /-- Convert JSON directly to S00 grammar syntax. The bound decreases at
  each block/statement edge. This is not static checking or admission. -/
  def blockAux : Nat → Json → Except Error (Syn (.list .yulStmt))
    | 0, _ => .error .depth
    | n + 1, j => do
      requireNode j "YulBlock"
      pure (toSynList (← ((← array j "statements").toList).mapM (statementAux n)))

  def statementAux : Nat → Json → Except Error (Syn .yulStmt)
    | 0, _ => .error .depth
    | n + 1, j => do
      let kind ← string j "nodeType"
      if kind = "YulBlock" then
        pure (.yulBlock (← blockAux n j))
      else if kind = "YulVariableDeclaration" then
        let vars ← names j "variables"
        let init ← match j.getObjVal? "value" with
          | .error _ => pure .none
          | .ok .null => pure .none
          | .ok value => pure (.some (← expressionAux n value))
        match vars with
        | [] => throw (.node "empty variable declaration")
        | first :: rest => pure (.yulLet first rest init)
      else if kind = "YulAssignment" then
        let paths ← ((← array j "variableNames").toList).mapM identifierPath
        let paths := paths.map (fun (head, tail) => head :: tail)
        match paths with
        | [] => throw (.node "empty assignment")
        | first :: rest => pure (.yulAssign first rest (← expressionAux n (← field j "value")))
      else if kind = "YulExpressionStatement" then
        pure (.yulExprStmt (← expressionAux n (← field j "expression")))
      else if kind = "YulIf" then
        pure (.yulIf (← expressionAux n (← field j "condition")) (← blockAux n (← field j "body")))
      else if kind = "YulForLoop" then
        pure (.yulFor (← blockAux n (← field j "pre"))
          (← expressionAux n (← field j "condition"))
          (← blockAux n (← field j "post")) (← blockAux n (← field j "body")))
      else if kind = "YulSwitch" then
        let selector ← expressionAux n (← field j "expression")
        let cases ← array j "cases"
        if cases.isEmpty then throw (.node "empty switch")
        let (cases, fallback) ← switchCases (blockAux n) cases.toList []
        pure (.yulSwitch selector cases fallback)
      else if kind = "YulFunctionDefinition" then
        let name ← string j "name"
        match yulTok (bytes name) with
        | some (.ident actual) =>
          if actual != name then throw (.identifier name)
        | _ => throw (.identifier name)
        pure (.yulFun name (← optionalNames j "parameters") (← optionalNames j "returnVariables")
          (← blockAux n (← field j "body")))
      else if kind = "YulBreak" then pure .yulBreak
      else if kind = "YulContinue" then pure .yulContinue
      else if kind = "YulLeave" then pure .yulLeave
      else throw (.node kind)
end

structure ParsedBlock (bound : Nat) (j : Json) where
  tree : Syn (.list .yulStmt)
  parsed : blockAux bound j = .ok tree

def parseBlock (bound : Nat) (j : Json) : Except Error (ParsedBlock bound j) :=
  match h : blockAux bound j with
  | .error e => .error e
  | .ok tree => .ok ⟨tree, h⟩

/-- Exact decoder equality only. Whole-block typing, source provenance,
admission and sufficiency of the input-derived bound are separate obligations. -/
def parseBlockText (raw : String) :
    Except Error ((j : Json) × ParsedBlock (raw.toUTF8.size + 1) j) := do
  let j ← (Json.parse raw).mapError Error.json
  pure ⟨j, ← parseBlock (raw.toUTF8.size + 1) j⟩



/-- JSON decoding plus the existing checked grammar's recursive shape check.
This still says nothing about lexical source provenance or whole-block typing. -/
structure ShapedBlock (bound : Nat) (j : Json) extends ParsedBlock bound j where
  shaped : tree.prec = true

def checkBlockShape (bound : Nat) (j : Json) : Except Error (ShapedBlock bound j) := do
  let parsed ← parseBlock bound j
  if h : parsed.tree.prec = true then pure ⟨parsed, h⟩
  else throw .shape

def checkBlockShapeText (raw : String) :
    Except Error ((j : Json) × ShapedBlock (raw.toUTF8.size + 1) j) := do
  let j ← (Json.parse raw).mapError Error.json
  pure ⟨j, ← checkBlockShape (raw.toUTF8.size + 1) j⟩

theorem ShapedBlock.contract {bound j} (b : ShapedBlock bound j) :
    blockAux bound j = .ok b.tree ∧ b.tree.prec = true :=
  ⟨b.parsed, b.shaped⟩


end Solidity.Frontend.YulJson
