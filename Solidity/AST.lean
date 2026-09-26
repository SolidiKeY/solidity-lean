import Lean
import Solidity.KeySort

/-!
# Types and names

The static vocabulary everything else is written in:

* the Solidity types (`PrimTy`, `Ty`, `RefTy`), their KeY sorts, and the
  struct table `structDef` the interpreter expands structs through;
* the operators, typed at the primitive type they accept;
* `Var`, a local variable: a name the program wrote, or a fresh one a rule
  declared (KeY's `\newLocalVars`), numbered so that it cannot clash
  (mini-solkey's `Ch02_Elab`).

The typed syntax built from these is `Syntax.lean`; the interpreter is
`Semantics.lean`.
-/

namespace Solidity

abbrev Name := String


/-- KeY `int, bool \extends Prim` (`intHeader.key`, `boolHeader.key`).
KeY has a single mathematical `int` sort; the calculus keeps solc's
`uint`/`int` distinction below `Prim` — both erase to KeY `int`
(range checking is `checkArith`'s job, not the sort's). -/
inductive PrimTy where
  | bool
  | uint
  | int
  deriving DecidableEq, Repr

mutual
  inductive RefTy where
    | struct (name : Name)
    | array (elem : Ty)
    | mapping (key value : Ty)
    deriving DecidableEq, Repr

  /-- KeY `Prim, Struct \extends StValue` (`solidityDLHeader.key`,
  `structHeader.key`): a type is a primitive sort or a reference sort. -/
  inductive Ty where
    | prim (p : PrimTy)
    | ref (ref : RefTy)
    deriving DecidableEq, Repr
end

instance : Coe PrimTy Ty := ⟨Ty.prim⟩

namespace Ty

/- Source-level names of the primitive types, usable in patterns.
The package and the `SolKey` reader match through these. -/
@[match_pattern] abbrev bool : Ty := .prim .bool
@[match_pattern] abbrev uint : Ty := .prim .uint
@[match_pattern] abbrev int : Ty := .prim .int

def isPrimitive : Ty -> Bool
  | prim _ => true
  | ref _ => false

def isReference (ty : Ty) : Bool :=
  !ty.isPrimitive

def indexElemTy : Ty -> Ty
  | Ty.ref (RefTy.array elem) => elem
  | Ty.ref (RefTy.mapping _ value) => value
  | _ => Ty.uint

end Ty

def PrimTy.isNumeric : PrimTy -> Bool
  | .uint | .int => true
  | .bool => false

mutual
  def Ty.allowsMemory : Ty -> Bool
    | Ty.ref ref => ref.allowsMemory
    | Ty.prim _ => true

  def RefTy.allowsMemory : RefTy -> Bool
    | RefTy.struct _ => true
    | RefTy.array elem => elem.allowsMemory
    | RefTy.mapping _ _ => false
end

/-! ### Solidity static types as KeY sorts

The three classifications solkey's Java applies to a static type, one
function each, so a Lean theorem can be read against the Java line it
mirrors. -/

/-- `MemoryReferenceTypes.isReferenceType`: a struct or an array is a
reference in memory (an `Identity`); a mapping is not — it cannot live
in memory at all. Shape-only, like the Java: an array *of* mappings
still counts. -/
def Ty.isMemoryReferenceType : Ty -> Bool
  | Ty.ref (RefTy.struct _) => true
  | Ty.ref (RefTy.array _) => true
  | _ => false

/-- `StorageReferenceTypes.isReferenceType`: "in storage, mappings are
reference-typed locations as well, unlike in memory". -/
def Ty.isStorageReferenceType (ty : Ty) : Bool :=
  ty.isReference

/-! ### The struct schema and `containsMapping`

The struct table and the type predicate that reads it live here rather than
in `Semantics.lean` because they are facts about *static types*, and the
typed AST needs one of them: `TypedStmt.Assign.mk` refuses a storage-to-storage
copy whose type carries a mapping, which is solkey's
`StorageReferenceTypes.containsMapping` behind `ParserUtils.parseAssignmentMaybe`
and solc's own rule since 0.7.  They keep the `Semantics` namespace, since
that is where every consumer names them. -/

namespace Semantics

/-! ## Struct schema

The union of the struct declarations of the ported solkey contracts:
`StandardExample.sol` / the standard example, `TestSuite.sol`, and the six
`solc/Solc*.sol` semantic-test ports. Names that recur across those
contracts (`Basket`, `Ledger`, `Pair`) agree on their members, so one
table serves all of them; the two that did not agree are renamed in the
port and noted at their arm. -/

/-- Struct definitions of the ported contracts.

The trailing catch-all is forced — the key is a `Name`, so the match
cannot be closed — and it is the one silent default left in this file: an
unknown struct name has zero fields, so `defaultForTy` builds an empty
node for it instead of being stuck.  Harmless while the contract corpus
is closed; making it loud would mean an `Option` result threaded through
`defaultForTy`, `tyHasMapping`, `Reachability` and `WellFormedConsumers`. -/
def structDef : Name -> List (Name × Ty)
  | "Token" => [("value", Ty.uint)]
  | "Account" =>
      [("balance", Ty.uint), ("token", Ty.ref (RefTy.struct "Token"))]
  | "Person" =>
      [("account", Ty.ref (RefTy.struct "Account")), ("age", Ty.uint)]
  -- A struct with a mapping member, exercising the delete/`delNode`
  -- semantics (mapping members survive `delete` on the struct).
  | "Wallet" =>
      [("owner", Ty.uint),
       ("stash", Ty.ref (RefTy.mapping Ty.uint Ty.uint))]
  -- TestSuite.sol (`keyext.solidity.examples/TestSuite.sol`); `Basket`
  -- is shared verbatim with `solc/SolcMemory.sol`.
  | "Basket" => [("items", Ty.ref (RefTy.array Ty.uint))]
  | "Ledger" =>
      [("nonce", Ty.uint),
       ("balances", Ty.ref (RefTy.mapping Ty.uint Ty.uint))]
  | "LedgerUse" => [("ledger", Ty.ref (RefTy.struct "Ledger"))]
  | "TokenBucket" =>
      [("tokens", Ty.ref (RefTy.array (Ty.ref (RefTy.struct "Token"))))]
  | "Toggle" => [("on", Ty.bool), ("n", Ty.uint)]
  -- solc/SolcArrays.sol, SolcControlFlow.sol, SolcStructs.sol (agree).
  | "Pair" => [("a", Ty.uint), ("b", Ty.uint)]
  -- solc/SolcMappings.sol.
  | "S" => [("a", Ty.uint)]
  | "Sub" => [("x", Ty.uint), ("y", Ty.uint)]
  | "WithSub" =>
      [("a", Ty.uint), ("sub", Ty.ref (RefTy.struct "Sub"))]
  -- solc/SolcMemory.sol.
  | "Inner" => [("a", Ty.uint), ("b", Ty.uint), ("c", Ty.uint)]
  | "Outer" => [("a", Ty.uint), ("s", Ty.ref (RefTy.struct "Inner"))]
  -- solc/SolcStructs.sol. Its `Flagged`/`Depth0`/`Depth1`/`Depth2`
  -- family is *not* here: `Depth0.recursive` and `Depth1.recursive` have
  -- different types, as do `Flagged.y` (bool) and `Sub.y`/`Triple.y`
  -- (uint), and field names resolve through the single global
  -- `SoliditySyntax.fieldTy` table, which has no room for an overload.
  -- The two functions that use them (`recursiveStructThroughAliases`,
  -- `nestedRecursiveStructSetAndCheck`) are recorded `unsupported`.
  | "Simple" => [("value", Ty.uint)]
  | "WithArray" =>
      [("n", Ty.uint), ("items", Ty.ref (RefTy.array Ty.uint))]
  | "Triple" => [("x", Ty.uint), ("y", Ty.uint), ("z", Ty.uint)]
  -- Not a ported contract: two rows for one field name, which no solc
  -- program can declare. It exists so `Counterexamples/`'s R3 can show
  -- that `defaultOk`'s no-duplicate-row condition is load-bearing —
  -- `defaultForTy` builds both rows, and the second has the wrong type
  -- for what the field name looks up to.
  | "BadDup" => [("a", Ty.uint), ("a", Ty.bool)]
  | _ => []

/-! ### The `structDef` termination certificate

`defaultForTy` and `tyHasMapping` expand a struct through the `structDef`
table, not into a structurally smaller `Ty`, so neither is structural.
They used to be fuelled at a hardcoded `8`, and fuel exhaustion was a
*silent wrong answer* — `SVal.int 0` for a struct, `false` for "contains
a mapping" — rather than an error.

`structRank` replaces that magic number with a certificate: a strict
upper bound on the rank of every field type of a struct.  A new struct
whose fields outrank it fails `structDef_rank_lt`, so table drift is a
build error instead of a wrong answer at depth 9. -/

/-- Strict upper bound on the rank of a struct's field types. -/
def structRank : Name -> Nat
  | "Token" => 1
  | "Account" => 2
  | "Person" => 3
  | "Wallet" => 1
  | "Basket" => 1
  | "Ledger" => 1
  | "LedgerUse" => 2
  | "TokenBucket" => 2
  | "Toggle" => 1
  | "Pair" => 1
  | "S" => 1
  | "Sub" => 1
  | "WithSub" => 2
  | "Inner" => 1
  | "Outer" => 2
  | "Simple" => 1
  | "WithArray" => 1
  | "Triple" => 1
  | "BadDup" => 1
  | _ => 1

/-- A type's rank: primitives 0, a struct its `structRank`, an array and
a mapping the rank of the type they expand into. -/
def tyRank : Ty -> Nat
  | Ty.prim _ => 0
  | Ty.ref (RefTy.struct n) => structRank n
  | Ty.ref (RefTy.array e) => tyRank e
  | Ty.ref (RefTy.mapping _ v) => tyRank v

def fieldsRank : List (Name × Ty) -> Nat
  | [] => 0
  | (_, t) :: rest => max (tyRank t) (fieldsRank rest)

theorem structRank_pos (n : Name) : 0 < structRank n := by
  unfold structRank; split <;> omega

/-- **The certificate.** Every field of a struct outranks nothing: its
rank is strictly below the struct's own.  Checked by `decide` against the
concrete table, so adding a struct whose fields are too deep for its
`structRank` row fails here. -/
theorem structDef_rank_lt (n : Name) :
    fieldsRank (structDef n) < structRank n := by
  unfold structDef
  split
  all_goals first
    | decide
    | simpa [fieldsRank] using structRank_pos _

/-- Lexicographic step when the first component may stay equal. -/
theorem lex_le_lt {a b x y : Nat} (hab : a ≤ b) (hxy : x < y) :
    Prod.Lex (· < ·) (· < ·) (a, x) (b, y) := by
  rcases Nat.lt_or_ge a b with h | h
  · exact Prod.Lex.left _ _ h
  · have he : a = b := Nat.le_antisymm hab h
    subst he; exact Prod.Lex.right _ hxy

mutual
/-- Does a type contain a (nested) mapping? solc ≥ 0.7 refuses to
compile a storage-to-storage assignment of such a type ("Types in
storage containing (nested) mappings cannot be assigned to"), so the
interpreter is stuck on one — the program does not exist. -/
def tyHasMapping : Ty -> Bool
  | Ty.prim _ => false
  | Ty.ref (RefTy.mapping _ _) => true
  | Ty.ref (RefTy.struct name) => fieldsHaveMapping (structDef name)
  | Ty.ref (RefTy.array elem) => tyHasMapping elem
termination_by ty => (tyRank ty, sizeOf ty)
decreasing_by
  · exact Prod.Lex.left _ _ (structDef_rank_lt _)
  · apply Prod.Lex.right; simp; omega

def fieldsHaveMapping : List (Name × Ty) -> Bool
  | [] => false
  | (_, t) :: rest => tyHasMapping t || fieldsHaveMapping rest
termination_by l => (fieldsRank l, sizeOf l)
decreasing_by
  all_goals (apply lex_le_lt
             · simp only [fieldsRank]; omega
             · simp; omega)
end

/-! ## Association-list helpers -/

def lookupBy [DecidableEq κ] (k : κ) : List (κ × α) -> Option α
  | [] => none
  | (k', v) :: rest => if k = k' then some v else lookupBy k rest

def setBy [DecidableEq κ] (k : κ) (v : α) : List (κ × α) -> List (κ × α)
  | [] => [(k, v)]
  | (k', v') :: rest =>
      if k = k' then (k, v) :: rest else (k', v') :: setBy k v rest

end Semantics

mutual
  /-- The KeY sort of a static type, as `SolidityInfo.registerPredefinedTypes`
  (`bool ↦ bool`; every `intN`/`uintN`, `address`, `string` ↦ `int`) and
  `SolJSONParser.getComponentSort` (struct ↦ `Struct`; `T[]` and
  `mapping(K => V)` ↦ their own sorts below `StValue`) assign it. With
  `memoryPayload` set, the type is read the way
  `FieldExpressionTypeToSortCondition`/`IndexedExpressionTypeToSortCondition`
  read a member or element held in memory: a memory reference type
  denotes an `Identity`; a mapping is not one and keeps its sort. -/
  def Ty.keySort (memoryPayload : Bool) : Ty -> KeySort
    | Ty.prim PrimTy.bool => KeySort.bool
    | Ty.prim _ => KeySort.int
    | Ty.ref ref => ref.keySort memoryPayload

  def RefTy.keySort (memoryPayload : Bool) : RefTy -> KeySort
    | RefTy.struct _ => if memoryPayload then KeySort.identity else KeySort.struct
    | RefTy.array elem =>
        if memoryPayload then KeySort.identity else KeySort.array (elem.keySort false)
    | RefTy.mapping key value =>
        KeySort.mapping (key.keySort false) (value.keySort false)
end

/-- `Ty.keySort` under the name the `SolKey` reader's decoder uses. -/
abbrev keySortOf (memoryPayload : Bool) (ty : Ty) : KeySort :=
  ty.keySort memoryPayload

/-- `\generic alphaPrim \extends Prim` binds exactly the primitive
types: the bound is `Ty.isPrimitive` by computation, not by fiat. -/
theorem Ty.keySort_le_prim (ty : Ty) :
    (ty.keySort false).le KeySort.prim = ty.isPrimitive := by
  cases ty with
  | prim p => cases p <;> rfl
  | ref r => cases r <;> rfl

/-- Every static type is storable: `\generic alphaSt \extends StValue`
binds all of them. -/
theorem Ty.keySort_le_stValue (ty : Ty) :
    (ty.keySort false).le KeySort.stValue = true := by
  cases ty with
  | prim p => cases p <;> rfl
  | ref r => cases r <;> rfl

/-- Read as a memory payload, a type that may live in memory is a
`MemValue` (`\generic alphaMem \extends MemValue`); a mapping is the
one type that is neither, and `allowsMemory` already excludes it. -/
theorem Ty.keySort_memory_le_memValue (ty : Ty) (h : ty.allowsMemory = true) :
    (ty.keySort true).le KeySort.memValue = true := by
  cases ty with
  | prim p => cases p <;> rfl
  | ref r =>
    cases r with
    | struct _ => rfl
    | array _ => rfl
    | mapping _ _ => simp [Ty.allowsMemory, RefTy.allowsMemory] at h

/-- `\generic alphaId \extends Identity` (under `\hasMemoryFieldSort`)
binds exactly the memory reference types — the Java's shape-only test,
so an array of mappings is admitted even though `allowsMemory` refuses it. -/
theorem Ty.keySort_memory_le_identity (ty : Ty) :
    (ty.keySort true).le KeySort.identity = ty.isMemoryReferenceType := by
  cases ty with
  | prim p => cases p <;> rfl
  | ref r => cases r <;> rfl

/-- KeY `MapField, RefField \extends Field` (`structHeader.key`): `ref`
marks a struct/array member (`RefField`), `map` a mapping member
(`MapField`), and `prim` a value member — which in KeY is a bare `Field`
with no subsort of its own. KeY used to spell that one `PrimField` (and
`ref` `IdField`); solkey `0f9b99ad55` dropped the primitive subsort, and
its rules now discriminate a value member by binding its declared type
under a `Prim` bound, `\varcond(\hasFieldSort(a, \sort(alphaPrim)))`,
rather than by sort. -/
inductive FieldSort where
  | prim
  | ref
  | map
  deriving DecidableEq, Repr

/-- The `Field` subsort a member of this reference sort inhabits. -/
def RefTy.fieldSort : RefTy -> FieldSort
  | RefTy.mapping _ _ => FieldSort.map
  | _ => FieldSort.ref

/-- `SolJSONParser.fieldSortFor`: the `Field` subsort a member's declared
type stamps on its field constant — `MapField` for a mapping, `RefField`
for a memory reference type (struct or array), the bare `Field` for a
value. -/
def Ty.fieldSort : Ty -> FieldSort
  | Ty.ref r => r.fieldSort
  | Ty.prim _ => FieldSort.prim

theorem Ty.fieldSort_ref (r : RefTy) : Ty.fieldSort (Ty.ref r) = r.fieldSort := rfl

/-- A member declaration (KeY `FieldDeclaration`): a name and a declared
type. Its `Field` subsort is not stored — it is `sort`, stamped from the
type exactly as `SolJSONParser.fieldSortFor` stamps the field constant,
so a field cannot be classified against its own type. -/
structure Field where
  name : Name
  ty : Ty
  deriving DecidableEq, Repr

namespace Field

/-- The `Field` subsort of this member, from its declared type. -/
def sort (field : Field) : FieldSort :=
  field.ty.fieldSort

/-- Value member (a bare `Field` in KeY). -/
def primitive (name : Name) (ty : Ty) : Field :=
  { name, ty }

/-- Reference member; classifies itself `RefField` vs `MapField` from
the target sort. -/
def identity (name : Name) (ref : RefTy := RefTy.struct name) : Field :=
  { name, ty := Ty.ref ref }

def isPrimitive (field : Field) : Bool :=
  field.sort matches FieldSort.prim

/-- A value member is exactly one whose declared type `\hasFieldSort`
binds under `\generic alphaPrim \extends Prim`. -/
theorem isPrimitive_eq_keySort_le_prim (field : Field) :
    field.isPrimitive = (field.ty.keySort false).le KeySort.prim := by
  rw [Ty.keySort_le_prim]
  unfold Field.isPrimitive Field.sort
  cases field.ty with
  | prim p => rfl
  | ref r => cases r <;> rfl

/-- Non-primitive member (`RefField ∪ MapField`) — the delete-target and
alias classifications in `Calculus/Rules.lean` bipartition on this, so it keeps
the pre-`FieldSort` meaning rather than `RefField` alone. -/
def isIdentity (field : Field) : Bool :=
  !field.isPrimitive

def isRefField (field : Field) : Bool :=
  field.sort matches FieldSort.ref

def isMapField (field : Field) : Bool :=
  field.sort matches FieldSort.map

end Field

/-- Binary operators of the KeY calculus (`solidityProgramRules.key`):
arithmetic (`addition` .. `modulo`), comparisons (`lessThan` ..
`greaterEqual`) and boolean connectives (`boolEquality`, `boolInequality`,
`logicalAnd`, `logicalOr`). -/
inductive BinOp where
  | add | sub | mul | pow | div | mod
  | lt | gt | le | ge
  | eqB | neB | and | or
  deriving DecidableEq, Repr

namespace BinOp

def isArith : BinOp -> Bool
  | add | sub | mul | pow | div | mod => true
  | _ => false

def isComparison : BinOp -> Bool
  | lt | gt | le | ge => true
  | _ => false

def isBoolean : BinOp -> Bool
  | eqB | neB | and | or => true
  | _ => false

/-- `/` and `%` revert on a zero divisor (KeY `division_unfold_result`,
`modulo_unfold_result`). -/
def needsGuard : BinOp -> Bool
  | div | mod => true
  | _ => false

/-- `&&` and `||` short-circuit: the right operand must not be hoisted
into a temporary ahead of the left (KeY defers these to the if rules, so
there is no `logicalAndCaptureRhs`/`logicalOrCaptureRhs` taclet). -/
def shortCircuits : BinOp -> Bool
  | and | or => true
  | _ => false

/-- Operators with a Solidity compound-assignment form (`+=` .. `%=`);
KeY has `storage{Root,Field,Index}{Add,Sub,Mul,Div,Mod}Assign` and no
`**=` rules. -/
def hasCompoundAssign : BinOp -> Bool
  | add | sub | mul | div | mod => true
  | _ => false

/-- Result type given the operand type: arithmetic preserves it,
comparisons and boolean connectives produce `bool`. -/
def retTy (op : BinOp) (operand : Ty) : Ty :=
  if op.isArith then operand else Ty.bool

end BinOp

/-- Unary operators: `unaryMinus*` and `logicalNot*` taclets. -/
inductive UnOp where
  | neg | not
  deriving DecidableEq, Repr

namespace UnOp

def retTy : UnOp -> Ty -> Ty
  | neg, operand => operand
  | not, _ => Ty.bool

end UnOp

/-- Prefix/postfix increment and decrement (`storageRootPreincrement`,
`localAssignPostdecrement`, ... taclet families). -/
inductive IncDec where
  | preInc | preDec | postInc | postDec
  deriving DecidableEq, Repr

namespace IncDec

def isPre : IncDec -> Bool
  | preInc | preDec => true
  | _ => false

def isIncrement : IncDec -> Bool
  | preInc | postInc => true
  | _ => false

/-- The underlying arithmetic operator: `++` adds, `--` subtracts. -/
def binOp (op : IncDec) : BinOp :=
  if op.isIncrement then BinOp.add else BinOp.sub

end IncDec

/-! ## The four shapes of a type

`Ty` is `prim | ref`, with the reference sorts one level down.  A case split
wants the four source-level shapes at once: `uint x`, `Person p`,
`uint[] xs`, `mapping(uint => uint) m`. -/

namespace Ty

@[match_pattern, reducible] def struct (n : Name) : Ty := .ref (.struct n)
@[match_pattern, reducible] def array (T : Ty) : Ty := .ref (.array T)
@[match_pattern, reducible] def mapping (K V : Ty) : Ty := .ref (.mapping K V)

/-- `cases T` by the four shapes a Solidity type is written in. -/
@[elab_as_elim]
def casesOn4 {motive : Ty → Sort u} (prim : ∀ p, motive (.prim p))
    (struct : ∀ n, motive (.struct n)) (array : ∀ T, motive (.array T))
    (mapping : ∀ K V, motive (.mapping K V)) : ∀ T, motive T
  | .prim p => prim p
  | .ref (.struct n) => struct n
  | .ref (.array T) => array T
  | .ref (.mapping K V) => mapping K V

end Ty

/-! ## Mapping-free types, well-formed defaults

A storage copy of a type that holds a mapping is rejected by solc, and a
fresh default must be well-formed.  `tyHasMapping` and `defaultOk` answer
these by well-founded recursion through `structDef`, which the kernel
cannot evaluate; `mapFree` and `defaultOkS` answer them structurally, so
their proofs are `Eq.refl`, from a list of the structs checked once
(`mapFree_sound` in `Typing/StoragePreservation.lean`). -/

/-- The structs of `structDef` that hold no mapping. -/
def mapFreeStructs : List Name :=
  ["Token", "Account", "Person", "Basket", "TokenBucket", "Toggle", "Pair", "S", "Sub",
   "WithSub", "Inner", "Outer", "Simple", "WithArray", "Triple", "BadDup"]

/-- `T` holds no mapping: `Person[]` does not, `mapping(uint => uint)` does. -/
def Ty.mapFree : Ty → Bool
  | .prim _ => true
  | .ref (.mapping ..) => false
  | .ref (.struct s) => s ∈ mapFreeStructs
  | .ref (.array e) => e.mapFree

/-- The structs whose fresh default is well-formed: all but `BadDup`, whose
second `a` row is the counterexample the condition exists for. -/
def defaultOkStructs : List Name :=
  ["Token", "Account", "Person", "Wallet", "Basket", "Ledger", "LedgerUse", "TokenBucket",
   "Toggle", "Pair", "S", "Sub", "WithSub", "Inner", "Outer", "Simple", "WithArray", "Triple"]

/-- `T`'s fresh default is well-formed: what `values.push();` and
`Person memory m;` need. -/
def Ty.defaultOkS : Ty → Bool
  | .prim _ => true
  | .ref (.struct s) => s ∈ defaultOkStructs
  | .ref (.array _) => true
  | .ref (.mapping _ v) => v.defaultOkS

/-! ## Operators at primitive types -/

/-- The primitive operand type an operator accepts: arithmetic and
comparisons on numbers, `&&`/`||` on booleans, `==`/`!=` on either. -/
def BinOp.accepts : BinOp → PrimTy → Bool
  | .and, p | .or, p => p == .bool
  | .eqB, _ | .neB, _ => true
  | _, p => p.isNumeric

/-- The result type at operand type `p`: `a + b` on `uint` is a `uint`,
`a < b` a `bool`. -/
def BinOp.ret (op : BinOp) (p : PrimTy) : PrimTy :=
  if op.isArith then p else .bool

def UnOp.accepts : UnOp → PrimTy → Bool
  | .neg, p => p.isNumeric
  | .not, p => p == .bool

/-- `-x` keeps its type, `!b` is a `bool`. -/
def UnOp.ret : UnOp → PrimTy → PrimTy
  | .neg, p => p
  | .not, _ => .bool

/-! ## Local variables

A local is a name the program wrote (`.user "x"`), or a variable a rule
declared (`.fresh "se" k`, KeY's `\newLocalVars`): `base` says what it holds
(`se` a value, `sp` a storage path, `ie` an index, `mv` a memory reference)
and `k` makes it fresh — a rule numbers its variables past every index in
the formula it rewrites.  How a fresh variable is spelled is up to
`FreshNames`; freshness is by index, so no proof depends on the spelling. -/

inductive Var where
  | user (s : String)
  | fresh (base : String) (k : Nat)
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

/-- How fresh variables are spelled: `name b k` spells `.fresh b k`, and
`parse` reads a spelling back, so a printed line can be pasted back.  The
default is `se1`, `sp1`, `ie1`, `mv1`; a file picks its own with
`local instance : FreshNames := .ofPrefixes "tmp" "ref" "idx" "mref"`. -/
class FreshNames where
  name : String → Nat → String
  parse : String → Option (String × Nat)

/-- The `k`-th fresh variable of each kind is a prefix and `k`.  The four
prefixes must be distinct identifiers that do not end in a digit. -/
def FreshNames.ofPrefixes (se sp ie mv : String) : FreshNames where
  name b k :=
    let pre := if b = "se" then se else if b = "sp" then sp else if b = "ie" then ie
      else if b = "mv" then mv else b
    s!"{pre}{k}"
  parse s :=
    let stem := s.takeWhile (!·.isDigit)
    let digits := s.drop stem.length
    if digits.isEmpty || !digits.all (·.isDigit) then none
    else ([("se", se), ("sp", sp), ("ie", ie), ("mv", mv)].find? (·.2 == stem)).map
      (·.1, digits.toNat!)

/-- `se1`, `sp1`, `ie1`, `mv1`, unless a file declares its own. -/
instance (priority := low) : FreshNames := .ofPrefixes "se" "sp" "ie" "mv"

instance [FreshNames] : ToString Var where
  toString
    | .user s => s
    | .fresh b k => FreshNames.name b k

/-- A name as written: a fresh variable if `FreshNames` reads it as one
(`se12`), any other name a user variable. -/
def Var.ofName [FreshNames] (s : String) : Var :=
  match FreshNames.parse s with
  | some (b, k) => .fresh b k
  | none => .user s

/-- The index of a variable: `k` for `.fresh _ k`, `0` for a user variable.
A rule declares its variables at an index past every one in the formula. -/
def Var.idx : Var → Nat
  | .user _ => 0
  | .fresh _ k => k

end Solidity
