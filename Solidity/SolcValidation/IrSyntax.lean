import Solidity.SolcValidation.Dialect

/-!
# Intrinsic syntax of solc's object-dialect Yul text

The typed tree that `--ir` / `--ir-optimized` text parses into
(`SolcValidation/IrParse.lean`). Contexts are lists of names: a local is a
positional membership in the names in scope, a call is a membership in the
visible function signatures, and every expression is indexed by its exact
number of returned words. Operations reuse the dialect's `Op` (core EVM
builtins plus the compiler-only object operations). `leave`, `break` and
`continue` are unrepresentable outside a function or loop. Function bodies see
only their parameters and returns, plus every visible function.

Names are kept as metadata so that the printer `objectToks` can reproduce the
source token stream exactly; this is what makes the parser certifying. The
types admit duplicate names; the checked `objectWf` (`SolcValidation/IrParse.lean`)
rules them out and fixes each reference to its unique binder. No
semantics is asserted here (see `SolcValidation/IrEval.lean`).
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

abbrev Word := Fin (2 ^ 256)

/-- Positional membership; the selected element is in the index. -/
inductive Mem {α : Type} : List α → α → Type where
  | here {a : α} {as : List α} : Mem (a :: as) a
  | there {a b : α} {as : List α} : Mem as a → Mem (b :: as) a
  deriving Repr

def Mem.index {α : Type} {as : List α} {a : α} : Mem as a → Nat
  | .here => 0
  | .there m => m.index + 1

/-- A function's exact name, parameter names and return names. -/
structure FnSig where
  name : String
  params : List String
  rets : List String
  deriving DecidableEq, Repr

/-- The control context: inside a function body, inside a loop body. -/
structure Ctl where
  function : Bool
  loop : Bool
  deriving DecidableEq, Repr

/-- Literal spellings as the lexer delivers them: numbers carry their value
(decimal and hexadecimal spellings coincide), strings their raw body. -/
inductive LitTok where
  | num (value : Nat)
  | str (raw : String)
  | bool (value : Bool)
  deriving DecidableEq, Repr

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def toByte? (n : Nat) : Option (Fin 256) :=
  if h : n < 256 then some ⟨n, h⟩ else none

/-- The byte of a simple backslash escape. -/
def escapeByte (c : Char) : Option (Fin 256) :=
  if c = '\\' then some 92 else if c = '"' then some 34 else if c = '\'' then some 39
  else if c = 'n' then some 10 else if c = 'r' then some 13 else if c = 't' then some 9
  else if c = 'b' then some 8 else if c = 'f' then some 12 else if c = 'v' then some 11
  else none

/-- UTF-8 bytes of a `\uNNNN` code point (at most three bytes). -/
def utf8Bytes (n : Nat) : List Nat :=
  if n < 0x80 then [n]
  else if n < 0x800 then [0xC0 + n / 64, 0x80 + n % 64]
  else [0xE0 + n / 4096, 0x80 + n / 64 % 64, 0x80 + n % 64]

/-- Bytes of a string literal body. Unescaped characters must be printable
ASCII; non-ASCII text is refused (open work, not accepted with a guessed
encoding). `\uNNNN` is encoded as UTF-8, as solc does. -/
def decodeString : List Char → Option (List (Fin 256))
  | [] => some []
  | '\\' :: 'x' :: h :: l :: rest => do
      let hi ← hexDigit? h
      let lo ← hexDigit? l
      let b ← toByte? (hi * 16 + lo)
      let tail ← decodeString rest
      pure (b :: tail)
  | '\\' :: 'u' :: a :: b :: c :: d :: rest => do
      let a ← hexDigit? a
      let b ← hexDigit? b
      let c ← hexDigit? c
      let d ← hexDigit? d
      let bytes ← (utf8Bytes (((a * 16 + b) * 16 + c) * 16 + d)).mapM toByte?
      let tail ← decodeString rest
      pure (bytes ++ tail)
  | '\\' :: c :: rest => do
      let b ← escapeByte c
      let tail ← decodeString rest
      pure (b :: tail)
  | '\\' :: [] => none
  | '"' :: _ => none
  | c :: rest => do
      let b ← if 32 ≤ c.toNat ∧ c.toNat < 127 then toByte? c.toNat else none
      let tail ← decodeString rest
      pure (b :: tail)

/-- Big-endian value of a byte sequence. -/
def bytesValue (bytes : List (Fin 256)) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.val) 0

/-- Yul string literals denote their bytes left-aligned in one word. -/
def stringWord (bytes : List (Fin 256)) : Option Word :=
  if bytes.length ≤ 32 then
    let v := bytesValue bytes * 256 ^ (32 - bytes.length)
    if h : v < 2 ^ 256 then some ⟨v, h⟩ else none
  else none

def LitTok.decode : LitTok → Option Word
  | .num n => if h : n < 2 ^ 256 then some ⟨n, h⟩ else none
  | .str raw => decodeString raw.toList >>= stringWord
  | .bool b => some (if b then 1 else 0)

/-- A literal with its decoded word; out-of-range numbers and strings longer
than a word are unrepresentable. -/
structure Lit where
  tok : LitTok
  value : Word
  decoded : tok.decode = some value

mutual
/-- Expressions over visible functions `F` and locals `L`, indexed by their
exact number of returned words. -/
inductive Expr : List FnSig → List String → Nat → Type where
  | lit {F L} : Lit → Expr F L 1
  | var {F L} (x : String) : Mem L x → Expr F L 1
  | op {F L a r} : Op a r → Args F L a → Expr F L r
  | call {F L} {s : FnSig} : Mem F s → Args F L s.params.length → Expr F L s.rets.length

/-- Single-valued argument lists of exact length. -/
inductive Args : List FnSig → List String → Nat → Type where
  | nil {F L} : Args F L 0
  | cons {F L k} : Expr F L 1 → Args F L k → Args F L (k + 1)
end

/-- An assignment target: a local already in scope. -/
abbrev Var (L : List String) := (x : String) × Mem L x

mutual
/-- Statements that do not open a binder over the rest of their block. -/
inductive Stmt : List FnSig → Ctl → List String → Type where
  | block {F c L} : Block F c L → Stmt F c L
  | discard {F c L} : Expr F L 0 → Stmt F c L
  | assign {F c L} (targets : List (Var L)) : Expr F L targets.length → Stmt F c L
  | if_ {F c L} : Expr F L 1 → Block F c L → Stmt F c L
  | switch {F c L} : Expr F L 1 → Cases F c L → Stmt F c L
  | switchDefault {F c L} : Expr F L 1 → Cases F c L → Block F c L → Stmt F c L
  | for_ {F c L} : Loop F c L → Stmt F c L
  | leave {F l L} : Stmt F ⟨true, l⟩ L
  | break_ {F f L} : Stmt F ⟨f, true⟩ L
  | continue_ {F f L} : Stmt F ⟨f, true⟩ L

inductive Cases : List FnSig → Ctl → List String → Type where
  | nil {F c L} : Cases F c L
  | cons {F c L} : Lit → Block F c L → Cases F c L → Cases F c L

/-- A `for` loop: its initialization items bind over the condition, the
post block and the body; `run` closes the initialization block. -/
inductive Loop : List FnSig → Ctl → List String → Type where
  | stmt {F c L} : Stmt F ⟨c.function, false⟩ L → Loop F c L → Loop F c L
  | let_ {F c L} (xs : List String) : Option (Expr F L xs.length) →
      Loop F c (xs ++ L) → Loop F c L
  | run {F c L} : Expr F L 1 → Block F ⟨c.function, false⟩ L →
      Block F ⟨c.function, true⟩ L → Loop F c L

/-- Block items. `let_` binds over the rest of the block; `fn k` marks where
the block's `k`-th (hoisted) function definition appears in the text. -/
inductive Items : List FnSig → Ctl → List String → Nat → Type where
  | nil {F c L g} : Items F c L g
  | stmt {F c L g} : Stmt F c L → Items F c L g → Items F c L g
  | let_ {F c L g} (xs : List String) : Option (Expr F L xs.length) →
      Items F c (xs ++ L) g → Items F c L g
  | fn {F c L g} : Fin g → Items F c L g → Items F c L g

/-- A block's function group is visible throughout the block and to every
body in the group. -/
inductive Block : List FnSig → Ctl → List String → Type where
  | mk {F c L} (ss : List FnSig) : Bodies (ss ++ F) ss →
      Items (ss ++ F) c L ss.length → Block F c L

inductive Bodies : List FnSig → List FnSig → Type where
  | nil {F} : Bodies F []
  | cons {F s ss} : Block F ⟨true, false⟩ (s.params ++ s.rets) → Bodies F ss →
      Bodies F (s :: ss)
end

/-- The code of an object: no visible functions, no locals, top control. -/
abbrev Code := Block [] ⟨false, false⟩ []

/-! ## Tokens and the printer -/

inductive Tok where
  | ident (s : String)
  | num (n : Nat)
  | str (raw : String)
  | hex (bytes : List (Fin 256))
  | lbrace | rbrace | lparen | rparen | comma | assign | arrow
  deriving DecidableEq, Repr

def commaSep : List (List Tok) → List Tok
  | [] => []
  | [x] => x
  | x :: xs => x ++ Tok.comma :: commaSep xs

def names (xs : List String) : List Tok := commaSep (xs.map fun x => [Tok.ident x])

def LitTok.toks : LitTok → List Tok
  | .num n => [.num n]
  | .str raw => [.str raw]
  | .bool b => [.ident (if b then "true" else "false")]

def callToks (name : String) (args : List (List Tok)) : List Tok :=
  .ident name :: .lparen :: commaSep args ++ [.rparen]

/-- Object operations print their literal metadata at its source position. -/
def objectOpToks : {a r : Nat} → ObjectOp a r → List (List Tok) → List Tok
  | _, _, .datasize l, _ => callToks "datasize" [[.str l]]
  | _, _, .dataoffset l, _ => callToks "dataoffset" [[.str l]]
  | _, _, .datacopy, args => callToks "datacopy" args
  | _, _, .setimmutable l, args => callToks "setimmutable" (args.take 1 ++ [[.str l]] ++ args.drop 1)
  | _, _, .loadimmutable l, _ => callToks "loadimmutable" [[.str l]]
  | _, _, .linkersymbol l, _ => callToks "linkersymbol" [[.str l]]
  | _, _, .memoryguard n, _ => callToks "memoryguard" [[.num n.val]]

def opToks : {a r : Nat} → Op a r → List (List Tok) → List Tok
  | _, _, .evm b, args => callToks b.name args
  | _, _, .object o, args => objectOpToks o args

mutual
def Expr.toks {F L r} : Expr F L r → List Tok
  | .lit l => l.tok.toks
  | .var x _ => [.ident x]
  | .op o args => opToks o args.toks
  | @Expr.call _ _ s _ args => callToks s.name args.toks

def Args.toks {F L k} : Args F L k → List (List Tok)
  | .nil => []
  | .cons e rest => e.toks :: rest.toks
end

def letToks {F L} (xs : List String) : Option (Expr F L xs.length) → List Tok
  | none => .ident "let" :: names xs
  | some e => .ident "let" :: names xs ++ .assign :: e.toks

def headerToks (s : FnSig) : List Tok :=
  .ident "function" :: .ident s.name :: .lparen :: names s.params ++ .rparen ::
    (if s.rets.isEmpty then [] else .arrow :: names s.rets)

mutual
def Stmt.toks {F c L} : Stmt F c L → List Tok
  | .block b => b.toks
  | .discard e => e.toks
  | .assign ts e => names (ts.map Sigma.fst) ++ .assign :: e.toks
  | .if_ e b => .ident "if" :: e.toks ++ b.toks
  | .switch e cs => .ident "switch" :: e.toks ++ cs.toks
  | .switchDefault e cs b => .ident "switch" :: e.toks ++ cs.toks ++ .ident "default" :: b.toks
  | .for_ lp => .ident "for" :: .lbrace :: lp.toks
  | .leave => [.ident "leave"]
  | .break_ => [.ident "break"]
  | .continue_ => [.ident "continue"]

def Cases.toks {F c L} : Cases F c L → List Tok
  | .nil => []
  | .cons l b rest => .ident "case" :: l.tok.toks ++ b.toks ++ rest.toks

def Loop.toks {F c L} : Loop F c L → List Tok
  | .stmt s rest => s.toks ++ rest.toks
  | .let_ xs e rest => letToks xs e ++ rest.toks
  | .run e post body => .rbrace :: e.toks ++ post.toks ++ body.toks

def Items.toks {F c L g} (fns : List (List Tok)) : Items F c L g → List Tok
  | .nil => []
  | .stmt s rest => s.toks ++ rest.toks fns
  | .let_ xs e rest => letToks xs e ++ rest.toks fns
  | .fn k rest => fns.getD k.val [] ++ rest.toks fns

def Block.toks {F c L} : Block F c L → List Tok
  | .mk _ bodies items => .lbrace :: items.toks bodies.toks ++ [.rbrace]

def Bodies.toks {F ss} : Bodies F ss → List (List Tok)
  | .nil => []
  | @Bodies.cons _ s _ body rest => (headerToks s ++ body.toks) :: rest.toks
end

mutual
def objectToks : Object Code → List Tok
  | .object name code children =>
      .ident "object" :: .str name :: .lbrace :: .ident "code" :: Block.toks code ++
        objectsToks children ++ [.rbrace]
  | .data name bytes => [.ident "data", .str name, .hex bytes]

def objectsToks : List (Object Code) → List Tok
  | [] => []
  | o :: os => objectToks o ++ objectsToks os
end

end Solidity.SolcValidation.IrSyntax
