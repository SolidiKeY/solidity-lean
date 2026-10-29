/-!
# The pinned source grammar as intrinsic syntax (S00)

The abstract syntax of Solidity 0.8.38, after the ANTLR grammar pinned by G00
(`docs/grammar/SolidityParser.g4` and `SolidityLexer.g4` at `argotorg/solidity`
commit `1835d247`, vendored as `tests/upstream/grammar-0.8.38/`).  It is
independent of the compiler, of the intrinsic programs (`Solidity.Syntax.*`)
and of the solc JSON importer: this module imports nothing.

**Intrinsic by category.**  `Syn c` is the syntax of category `c`: one
category per grammar rule that carries structure, with `Cat.list` and
`Cat.opt` for the grammar's repetitions and options.  A slot of the grammar
holds exactly the category the rule names, so an expression can never stand
where a statement or a type name is expected.

**Intrinsic contexts.**  Statements are indexed by `SCtx`: whether they are
inside a loop and inside an `unchecked` block.  `break` and `continue` exist
only inside a loop, and an `unchecked` block only outside another one, as
solc's syntax checker requires (the ANTLR grammar alone allows both
anywhere).  A function body starts outside both.

**Repetition with a minimum.**  Where the grammar requires at least one
element (`Struct` members, `enum` values, import aliases, call options, inline
arrays, catch clauses, …) the constructor takes the first element apart from
the rest.  Flags the grammar allows at most once (`virtual`, a visibility,
`override`, …) are an `Option` or a `Bool`; their source order is lexical
detail (G08–G11).

**Out of the profile but present.**  Inline assembly, with its Yul body,
`layout at`, the `>>>` operators and the `years` unit are syntax here, so a
program using them is represented and rejected precisely (`Syn.rejections`,
`Solidity/Source/Ctor.lean`).  The Yul body follows the grammar's rules
without its single- versus multi-variable restrictions, the non-empty
paths of an assignment, the function-call-only expression statement and the
"a case or a default" of `switch`; assembly is rejected whole except the
canonical rethrow (`Syn.excl`), which these approximations do not reach.

**Lexical content.**  Identifiers are strings, number literals their exact
value (underscores and spelling are lexical, G08), string literals the bytes
of their concatenated fragments.  `int`/`uint` are `int256`/`uint256`.
Fixed-point type names carry solc's bounds (`FixDims`).  Paths, pragma words
and identifiers are not checked non-empty: that is lexical (G08).

The constructor index and the mapping to the grammar's rules and labelled
alternatives are in `Solidity/Source/Ctor.lean`.
-/

namespace Solidity.Source

/-- A dotted name: `identifierPath` (`identifier (Period identifier)*`). -/
structure IdPath where
  head : String
  tail : List String := []
  deriving DecidableEq, Repr

/-- The `M`, `N` of a `fixedMxN`/`ufixedMxN` token inside solc's bounds
(`8 ≤ M ≤ 256`, `8 ∣ M`, `N ≤ 80`): solc's scanner reads any other spelling
as an identifier (`liblangutil/Token.cpp`, `fromIdentifierOrKeyword`).  The
ANTLR lexer's own token (`[1-9][0-9]*` digits, and two or more for
`ufixed`) differs; solc decides. -/
structure FixDims where
  bits : Nat
  digits : Nat
  valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 ∧ digits ≤ 80
  deriving DecidableEq, Repr

/-- An elementary type name (`elementaryTypeName`).  Integer widths and
`bytesN` lengths are the lexer's tokens, so their bounds are part of the
constructor. -/
inductive Elem where
  | address
  | addressPayable
  | bool
  | string
  | bytes
  /-- `intM`/`uintM` (`SignedIntegerType`/`UnsignedIntegerType`). -/
  | int (signed : Bool) (bits : Nat) (h : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
  /-- `bytesN` (`FixedBytes`). -/
  | fixedBytes (n : Nat) (h : 1 ≤ n ∧ n ≤ 32)
  /-- `fixed`/`ufixed` (`none`, an alias of `M = 128`, `N = 18`), or
  `fixedMxN`/`ufixedMxN` (`Fixed`/`Ufixed`). -/
  | fixed (signed : Bool) (dims : Option FixDims)
  deriving DecidableEq, Repr

/-- `visibility`. -/
inductive Visibility where
  | internal | external | priv | pub
  deriving DecidableEq, Repr

/-- `stateMutability`. -/
inductive Mutability where
  | pure | view | payable
  deriving DecidableEq, Repr

/-- A constructor's visibility (`internal`/`public`, obsolete but in the
grammar). -/
inductive CtorVis where
  | internal | pub
  deriving DecidableEq, Repr

/-- A state variable's visibility: the grammar admits no `external`. -/
inductive StateVis where
  | pub | priv | internal
  deriving DecidableEq, Repr

/-- `constant` or `immutable`. -/
inductive Constness where
  | constant | immutable
  deriving DecidableEq, Repr

/-- `dataLocation`. -/
inductive DataLoc where
  | memory | storage | calldata
  deriving DecidableEq, Repr

/-- The name position of `functionDefinition`: an identifier, or the
keywords `fallback`/`receive` (solc's parser accepts these with warning 3445,
declaring an ordinary function so named). -/
inductive FnName where
  | ident (name : String)
  | fallback
  | receive
  deriving DecidableEq, Repr

/-- `userDefinableOperator`. -/
inductive UserOp where
  | bitAnd | bitNot | bitOr | bitXor | add | div | mod | mul | sub
  | eq | gt | ge | lt | le | ne
  deriving DecidableEq, Repr

/-- `SubDenomination`. -/
inductive Denom where
  | wei | gwei | ether | seconds | minutes | hours | days | weeks | years
  deriving DecidableEq, Repr

/-- A number literal (`DecimalNumber`/`HexNumber`).  A decimal denotes
`mantissa / 10^fracDigits * 10^exp` (one value has several spellings; the
spelling is lexical, G08); a hexadecimal keeps its digits (their count types
an address literal) and whether its letter case is a valid EIP-55 checksum,
which the lexer computes from the spelling (G08). -/
inductive NumLit where
  | dec (mantissa fracDigits : Nat) (exp : Int)
  | hex (digits : List (Fin 16)) (checksummed : Bool)
  deriving DecidableEq, Repr

/-- `literal`: string, hex string, unicode string, boolean or number. -/
inductive Lit where
  /-- A string literal's bytes after escapes: `\xNN` may make them invalid
  UTF-8, so they are bytes, not a `String`. -/
  | str (bytes : List UInt8)
  | hexStr (bytes : List UInt8)
  | unicodeStr (bytes : List UInt8)
  | bool (b : Bool)
  | num (n : NumLit)
  deriving DecidableEq, Repr

/-- `UnaryPrefixOperation`'s operators. -/
inductive PrefixOp where
  | inc | dec | not | bitNot | delete | neg
  deriving DecidableEq, Repr

/-- `UnarySuffixOperation`'s operators. -/
inductive SuffixOp where
  | inc | dec
  deriving DecidableEq, Repr

/-- `MulDivModOperation`'s operators. -/
inductive MulOp where
  | mul | div | mod
  deriving DecidableEq, Repr

/-- `AddSubOperation`'s operators. -/
inductive AddOp where
  | add | sub
  deriving DecidableEq, Repr

/-- `ShiftOperation`'s operators: `<<`, `>>` and `>>>` (`Shr`). -/
inductive ShiftOp where
  | shl | sar | shr
  deriving DecidableEq, Repr

/-- `OrderComparison`'s operators. -/
inductive OrderOp where
  | lt | gt | le | ge
  deriving DecidableEq, Repr

/-- `EqualityComparison`'s operators. -/
inductive EqOp where
  | eq | ne
  deriving DecidableEq, Repr

/-- `assignOp`. -/
inductive AssignOp where
  | assign | bitOr | bitXor | bitAnd | shl | sar | shr | add | sub | mul | div | mod
  deriving DecidableEq, Repr

/-- `mappingKeyType`: an elementary type without `payable`, or a path. -/
inductive MapKey where
  | elem (e : Elem) (h : e ≠ .addressPayable)
  | path (p : IdPath)
  deriving DecidableEq, Repr

/-- `yulLiteral`. -/
inductive YulLit where
  | dec (n : Nat)
  | hex (n : Nat)
  | str (bytes : List UInt8)
  | hexStr (bytes : List UInt8)
  | bool (b : Bool)
  deriving DecidableEq, Repr

/-- The context of a statement: inside a loop, inside `unchecked`. -/
structure SCtx where
  loop : Bool
  unchecked : Bool
  deriving DecidableEq, Repr

/-- The context of a function, modifier or constructor body. -/
def SCtx.body : SCtx := ⟨false, false⟩

/-- The syntactic categories. `part top` is a `contractBodyElement` (or a
top-level declaration when `top`). -/
inductive Cat where
  | unit
  | top
  | importAlias
  | part (top : Bool)
  | inherit
  | callArgs
  | namedArg
  | modInv
  | param
  | structMember
  | eventParam
  | errorParam
  | usingAlias
  | using
  | fallbackSig
  | typeName
  | varDecl
  | expr
  | simple
  | stmt (k : SCtx)
  | item (k : SCtx)
  | block (k : SCtx)
  | catchClause (k : SCtx)
  | yulStmt
  | yulExpr
  | yulCase
  | list (c : Cat)
  | opt (c : Cat)
  deriving DecidableEq, Repr

/-- The syntax of each category. -/
inductive Syn : Cat → Type where
  -- Repetition and option.
  | nil {c : Cat} : Syn (.list c)
  | cons {c : Cat} : Syn c → Syn (.list c) → Syn (.list c)
  | none {c : Cat} : Syn (.opt c)
  | some {c : Cat} : Syn c → Syn (.opt c)
  -- `sourceUnit` and its elements.
  | unit : Syn (.list .top) → Syn .unit
  /-- `pragma …;`: the pragma's words, comments and whitespace removed
  (`pragma solidity ^0.8.0;` is `["solidity", "^0.8.0"]`). -/
  | pragma (words : List String) : Syn .top
  /-- `import "p" (as a)?;` -/
  | importPath (path : String) (alias : Option String) : Syn .top
  /-- `import {a as b, …} from "p";` -/
  | importSymbols : Syn .importAlias → Syn (.list .importAlias) → (path : String) → Syn .top
  /-- `import * as a from "p";` -/
  | importStar (alias path : String) : Syn .top
  | importAlias (symbol : String) (alias : Option String) : Syn .importAlias
  /-- `abstract? contract C (layout at e)? (is …)? { … }` -/
  | contract (abstract : Bool) (name : String) : Syn (.opt .expr) → Syn (.list .inherit) →
      Syn (.list (.part false)) → Syn .top
  | interface (name : String) : Syn (.list .inherit) → Syn (.list (.part false)) → Syn .top
  | library (name : String) : Syn (.list (.part false)) → Syn .top
  /-- A top-level function, constant, struct, enum, value type, error, event
  or `using`. -/
  | topPart : Syn (.part true) → Syn .top
  | inherit (base : IdPath) : Syn (.opt .callArgs) → Syn .inherit
  -- Contract body elements.
  | constructor : Syn (.list .param) → Syn (.list .modInv) → (payable : Bool) →
      (vis : Option CtorVis) → Syn (.block .body) → Syn (.part false)
  | function {t : Bool} (name : FnName) : Syn (.list .param) → (vis : Option Visibility) →
      (mutability : Option Mutability) → Syn (.list .modInv) → (virtual : Bool) →
      (override : Option (List IdPath)) → (returns : Syn (.list .param)) →
      Syn (.opt (.block .body)) → Syn (.part t)
  | modifier (name : String) : Syn (.opt (.list .param)) → (virtual : Bool) →
      (override : Option (List IdPath)) → Syn (.opt (.block .body)) → Syn (.part false)
  | fallback : Syn .fallbackSig → (external : Bool) → (mutability : Option Mutability) →
      Syn (.list .modInv) → (virtual : Bool) → (override : Option (List IdPath)) →
      Syn (.opt (.block .body)) → Syn (.part false)
  /-- `fallback()`: no parameters, so no `returns`. -/
  | fbNoParams : Syn .fallbackSig
  /-- `fallback(p, …) (returns (…))?` -/
  | fbParams : Syn .param → Syn (.list .param) → (returns : Syn (.list .param)) → Syn .fallbackSig
  | receive (external : Bool) (payable : Bool) : Syn (.list .modInv) → (virtual : Bool) →
      (override : Option (List IdPath)) → Syn (.opt (.block .body)) → Syn (.part false)
  | struct {t : Bool} (name : String) : Syn .structMember → Syn (.list .structMember) → Syn (.part t)
  | structMember : Syn .typeName → (name : String) → Syn .structMember
  | enum {t : Bool} (name : String) (first : String) (rest : List String) : Syn (.part t)
  /-- `type T is V;` -/
  | udvt {t : Bool} (name : String) (underlying : Elem) : Syn (.part t)
  | stateVar : Syn .typeName → (vis : Option StateVis) → (const : Option Constness) →
      (override : Option (List IdPath)) → (transient : Bool) → (name : String) →
      Syn (.opt .expr) → Syn (.part false)
  /-- A file-level `T constant x = e;` -/
  | constant : Syn .typeName → (name : String) → Syn .expr → Syn (.part true)
  | event {t : Bool} (name : String) : Syn (.list .eventParam) → (anonymous : Bool) → Syn (.part t)
  | eventParam : Syn .typeName → (indexed : Bool) → (name : Option String) → Syn .eventParam
  | error {t : Bool} (name : String) : Syn (.list .errorParam) → Syn (.part t)
  | errorParam : Syn .typeName → (name : Option String) → Syn .errorParam
  | usingPart {t : Bool} : Syn .using → Syn (.part t)
  /-- `using L for T global?;` (`for *` when the type is absent). -/
  | usingPath (lib : IdPath) : Syn (.opt .typeName) → (global : Bool) → Syn .using
  /-- `using {f as op, …} for T global?;` -/
  | usingAliases : Syn .usingAlias → Syn (.list .usingAlias) → Syn (.opt .typeName) →
      (global : Bool) → Syn .using
  | usingAlias (fn : IdPath) (op : Option UserOp) : Syn .usingAlias
  -- Arguments, modifiers and parameters.
  | positional : Syn (.list .expr) → Syn .callArgs
  | named : Syn (.list .namedArg) → Syn .callArgs
  | namedArg (name : String) : Syn .expr → Syn .namedArg
  | modInv (name : IdPath) : Syn (.opt .callArgs) → Syn .modInv
  | param : Syn .typeName → (loc : Option DataLoc) → (name : Option String) → Syn .param
  -- Type names.
  | elem (e : Elem) : Syn .typeName
  | fnType : Syn (.list .param) → (vis : Option Visibility) → (mutability : Option Mutability) →
      (returns : Syn (.list .param)) → Syn .typeName
  | mapping (key : MapKey) (keyName : Option String) : Syn .typeName →
      (valueName : Option String) → Syn .typeName
  | userType (path : IdPath) : Syn .typeName
  | array : Syn .typeName → Syn (.opt .expr) → Syn .typeName
  | varDecl : Syn .typeName → (loc : Option DataLoc) → (name : String) → Syn .varDecl
  -- Expressions, one constructor per labelled alternative.
  | index : Syn .expr → Syn (.opt .expr) → Syn .expr
  | slice : Syn .expr → Syn (.opt .expr) → Syn (.opt .expr) → Syn .expr
  /-- `e.name` (also `e.address`). -/
  | member : Syn .expr → (name : String) → Syn .expr
  | callOptions : Syn .expr → Syn .namedArg → Syn (.list .namedArg) → Syn .expr
  | call : Syn .expr → Syn .callArgs → Syn .expr
  | payableConv : Syn .callArgs → Syn .expr
  | metaType : Syn .typeName → Syn .expr
  | unaryPrefix (op : PrefixOp) : Syn .expr → Syn .expr
  | unarySuffix (op : SuffixOp) : Syn .expr → Syn .expr
  | exp : Syn .expr → Syn .expr → Syn .expr
  | mulDivMod (op : MulOp) : Syn .expr → Syn .expr → Syn .expr
  | addSub (op : AddOp) : Syn .expr → Syn .expr → Syn .expr
  | shift (op : ShiftOp) : Syn .expr → Syn .expr → Syn .expr
  | bitAnd : Syn .expr → Syn .expr → Syn .expr
  | bitXor : Syn .expr → Syn .expr → Syn .expr
  | bitOr : Syn .expr → Syn .expr → Syn .expr
  | order (op : OrderOp) : Syn .expr → Syn .expr → Syn .expr
  | equality (op : EqOp) : Syn .expr → Syn .expr → Syn .expr
  | and : Syn .expr → Syn .expr → Syn .expr
  | or : Syn .expr → Syn .expr → Syn .expr
  | cond : Syn .expr → Syn .expr → Syn .expr → Syn .expr
  | assign (op : AssignOp) : Syn .expr → Syn .expr → Syn .expr
  | new : Syn .typeName → Syn .expr
  /-- `(e?, …)`: at least one, possibly empty, component; `(e)` is a
  parenthesized expression. -/
  | tuple : Syn (.opt .expr) → Syn (.list (.opt .expr)) → Syn .expr
  | inlineArray : Syn .expr → Syn (.list .expr) → Syn .expr
  | ident (name : String) : Syn .expr
  | lit (l : Lit) : Syn .expr
  | litUnit (n : NumLit) (u : Denom) : Syn .expr
  /-- An elementary type name as an expression (`elementaryTypeName[false]`:
  no `address payable`). -/
  | elemType (e : Elem) (h : e ≠ .addressPayable) : Syn .expr
  -- Simple statements.
  | declVar : Syn .varDecl → Syn (.opt .expr) → Syn .simple
  /-- `(, , T x, , U y) = e;`: the leading holes, the first declaration, the
  remaining slots. -/
  | declTuple (holes : Nat) : Syn .varDecl → Syn (.list (.opt .varDecl)) → Syn .expr → Syn .simple
  | exprStmt : Syn .expr → Syn .simple
  -- Statements in context.
  | blockStmt {k : SCtx} : Syn (.block k) → Syn (.stmt k)
  | simpleStmt {k : SCtx} : Syn .simple → Syn (.stmt k)
  | ifStmt {k : SCtx} : Syn .expr → Syn (.stmt k) → Syn (.opt (.stmt k)) → Syn (.stmt k)
  | forStmt {l u : Bool} : Syn (.opt .simple) → Syn (.opt .expr) → Syn (.opt .expr) →
      Syn (.stmt ⟨true, u⟩) → Syn (.stmt ⟨l, u⟩)
  | whileStmt {l u : Bool} : Syn .expr → Syn (.stmt ⟨true, u⟩) → Syn (.stmt ⟨l, u⟩)
  | doWhile {l u : Bool} : Syn (.stmt ⟨true, u⟩) → Syn .expr → Syn (.stmt ⟨l, u⟩)
  | continueStmt {u : Bool} : Syn (.stmt ⟨true, u⟩)
  | breakStmt {u : Bool} : Syn (.stmt ⟨true, u⟩)
  /-- `try e (returns (…))? { … } catch …`: one or more clauses. -/
  | tryStmt {k : SCtx} : Syn .expr → (returns : Syn (.list .param)) → Syn (.block k) →
      Syn (.catchClause k) → Syn (.list (.catchClause k)) → Syn (.stmt k)
  | catchPlain {k : SCtx} : Syn (.block k) → Syn (.catchClause k)
  /-- `catch Name? (p, …) { … }` -/
  | catchSig {k : SCtx} (name : Option String) : Syn .param → Syn (.list .param) →
      Syn (.block k) → Syn (.catchClause k)
  | returnStmt {k : SCtx} : Syn (.opt .expr) → Syn (.stmt k)
  | emit {k : SCtx} : Syn .expr → Syn .callArgs → Syn (.stmt k)
  | revert {k : SCtx} : Syn .expr → Syn .callArgs → Syn (.stmt k)
  /-- `assembly "evmasm"? ("flag", …)? { … }` -/
  | assembly {k : SCtx} (evmasm : Bool) (flags : List String) : Syn (.list .yulStmt) → Syn (.stmt k)
  -- Blocks: statements and `unchecked` blocks, which do not nest.
  | block {k : SCtx} : Syn (.list (.item k)) → Syn (.block k)
  | stmtItem {k : SCtx} : Syn (.stmt k) → Syn (.item k)
  | uncheckedItem {l : Bool} : Syn (.block ⟨l, true⟩) → Syn (.item ⟨l, false⟩)
  -- Yul (inline assembly bodies; outside the profile).
  | yulBlock : Syn (.list .yulStmt) → Syn .yulStmt
  | yulLet (first : String) (rest : List String) : Syn (.opt .yulExpr) → Syn .yulStmt
  | yulAssign (first : List String) (rest : List (List String)) : Syn .yulExpr → Syn .yulStmt
  | yulExprStmt : Syn .yulExpr → Syn .yulStmt
  | yulIf : Syn .yulExpr → Syn (.list .yulStmt) → Syn .yulStmt
  | yulFor : Syn (.list .yulStmt) → Syn .yulExpr → Syn (.list .yulStmt) → Syn (.list .yulStmt) →
      Syn .yulStmt
  | yulSwitch : Syn .yulExpr → Syn (.list .yulCase) → Syn (.opt (.list .yulStmt)) → Syn .yulStmt
  | yulCase (l : YulLit) : Syn (.list .yulStmt) → Syn .yulCase
  | yulLeave : Syn .yulStmt
  | yulBreak : Syn .yulStmt
  | yulContinue : Syn .yulStmt
  | yulFun (name : String) (args rets : List String) : Syn (.list .yulStmt) → Syn .yulStmt
  | yulPath (head : String) (tail : List String) : Syn .yulExpr
  | yulCall (fn : String) : Syn (.list .yulExpr) → Syn .yulExpr
  | yulLit (l : YulLit) : Syn .yulExpr

end Solidity.Source
