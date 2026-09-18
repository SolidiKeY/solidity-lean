import Lean
import Solidity.KeySort

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

inductive StorageOrigin where
  | local
  | global
  deriving DecidableEq, Repr

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
  origin : Option StorageOrigin := none
  deriving DecidableEq, Repr

namespace Field

/-- The `Field` subsort of this member, from its declared type. -/
def sort (field : Field) : FieldSort :=
  field.ty.fieldSort

/-- Value member (a bare `Field` in KeY). -/
def primitive (name : Name) (ty : Ty)
    (origin : Option StorageOrigin := none) : Field :=
  { name, ty, origin }

/-- Reference member; classifies itself `RefField` vs `MapField` from
the target sort. -/
def identity (name : Name) (ref : RefTy := RefTy.struct name)
    (origin : Option StorageOrigin := none) : Field :=
  { name, ty := Ty.ref ref, origin }

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
alias classifications in `Rules.lean` bipartition on this, so it keeps
the pre-`FieldSort` meaning rather than `RefField` alone. -/
def isIdentity (field : Field) : Bool :=
  !field.isPrimitive

def isRefField (field : Field) : Bool :=
  field.sort matches FieldSort.ref

def isMapField (field : Field) : Bool :=
  field.sort matches FieldSort.map

end Field

inductive Kind where
  | storage
  | memory
  | stack
  deriving DecidableEq, Repr

namespace Kind

def isDataLocation : Kind -> Bool
  | storage => true
  | memory => true
  | stack => false

end Kind

/-- The KeY sort of a *local variable* of this kind and type —
`MemoryReferenceTypes.asLocalVariableType`, which re-sorts a storage
local of reference type to `List` (`asStorageAliasType`: it denotes the
path, not the value) and a memory local of reference type to
`Identity` (`asMemoryReferenceType`). A stack (`DataLocation.Default`)
variable keeps its type's sort. -/
def localVarSort (kind : Kind) (ty : Ty) : KeySort :=
  match kind with
  | Kind.storage => if ty.isStorageReferenceType then KeySort.list else ty.keySort false
  | Kind.memory => if ty.isMemoryReferenceType then KeySort.identity else ty.keySort false
  | Kind.stack => ty.keySort false

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

def ExprCallOk (kind : Kind) (ty : Ty) : Prop :=
  kind ≠ Kind.storage ∧
    (kind = Kind.stack -> ty.isPrimitive = true) ∧
    (kind = Kind.memory -> ty.isReference ∧ ty.allowsMemory = true)


namespace Typed

/-- A member holding a `Prim` value: in KeY a bare `Field` whose declared
type sits below `Prim` (`\hasFieldSort(a, \sort(alphaPrim))`); there is no
`PrimField` subsort upstream any more, the name here records what the
`PrimTy` index says. The old `ty.isPrimitive` proof became structure. -/
structure PrimField (base : RefTy) (p : PrimTy) where
  name : Name
  deriving Repr

/-- KeY `RefField`: a struct/array member (a child tree node). -/
structure RefField (base ref : RefTy) where
  name : Name
  refSort : ref.fieldSort = FieldSort.ref
  deriving Repr

/-- KeY `MapField`: a mapping member. Unlike KeY, where `MapField`
lives in storage only, this stays kind-generic like the old `fieldRef`:
structs always `allowsMemory`, even with mapping members — mapping
*access* is still storage-only via `mappingIndex`. -/
structure MapField (base : RefTy) (key value : Ty) where
  name : Name
  deriving Repr

mutual
  inductive Place : Kind -> Ty -> Type where
    | storageVar (name : Name) (ref : RefTy) :
        Place Kind.storage (Ty.ref ref)
    | memoryVar (name : Name) (ref : RefTy) :
        ref.allowsMemory = true ->
          Place Kind.memory (Ty.ref ref)
    | stackVar (name : Name) (ty : Ty) :
        ty.isPrimitive = true ->
          Place Kind.stack ty
    | fieldRef {kind base ref : _} :
        Place kind (Ty.ref base) ->
          RefField base ref ->
            Place kind (Ty.ref ref)
    | fieldMap {kind base key value : _} :
        Place kind (Ty.ref base) ->
          MapField base key value ->
            Place kind (Ty.ref (RefTy.mapping key value))
    | fieldPrim {kind base : _} {p : PrimTy} :
        Place kind (Ty.ref base) ->
          PrimField base p ->
            Place kind (Ty.prim p)
    | arrayIndex {kind elem : _} :
        Place kind (Ty.ref (RefTy.array elem)) ->
          Expr Kind.stack Ty.uint ->
            Place kind elem
    | mappingIndex {key value : _} :
        Place Kind.storage (Ty.ref (RefTy.mapping key value)) ->
          Expr Kind.stack key ->
            Place Kind.storage value
    deriving Repr

  inductive Expr : Kind -> Ty -> Type where
    | place {kind ty : _} :
        Place kind ty -> Expr kind ty
    | bool (value : Bool) :
        Expr Kind.stack Ty.bool
    | call (kind : Kind) (ty : Ty) (name : Name) (args : List WrappedExpr)
        {ok : ExprCallOk kind ty} :
        Expr kind ty
    | and :
        Expr Kind.stack Ty.bool ->
        Expr Kind.stack Ty.bool ->
          Expr Kind.stack Ty.bool
    deriving Repr

  inductive WrappedExpr where
    | var (kind : Kind) (ty : Ty) (field : Field)
    | field (kind : Kind) (ty : Ty) (base : WrappedExpr) (field : Field)
    | index (kind : Kind) (ty : Ty) (base index : WrappedExpr)
    | pushPlace (target : WrappedExpr)
    | bool (value : Bool)
    | intLit (ty : Ty) (value : Int)
    | mkCall (kind : Kind) (ty : Ty) (name : Name) (args : List WrappedExpr)
    | mkBinop (op : BinOp) (lhs rhs : WrappedExpr)
    | mkUnop (op : UnOp) (arg : WrappedExpr)
    | mkIncDec (op : IncDec) (target : WrappedExpr)
    /-- `cond ? thn : els` — KeY `ternaryCaptureCond`/`ternaryToIf`. -/
    | mkTernary (cond thn els : WrappedExpr)
    deriving Repr
end

namespace WrappedExpr

@[match_pattern] abbrev call (kind : Kind) (ty : Ty) (name : Name)
    (args : List WrappedExpr) {ok : ExprCallOk kind ty} : WrappedExpr :=
  let _proof : ExprCallOk kind ty := ok
  WrappedExpr.mkCall kind ty name args

abbrev and (kind : Kind) (ty : Ty)
    (lhs rhs : WrappedExpr)
    {kind_ok : kind = Kind.stack}
    {ty_ok : ty = Ty.bool} : WrappedExpr :=
  let _kind_proof : kind = Kind.stack := kind_ok
  let _ty_proof : ty = Ty.bool := ty_ok
  WrappedExpr.mkBinop BinOp.and lhs rhs

end WrappedExpr

def RefField.toField {base ref : RefTy} (field : RefField base ref) : Field :=
  Field.identity field.name ref

def MapField.toField {base : RefTy} {key value : Ty}
    (field : MapField base key value) : Field :=
  Field.identity field.name (RefTy.mapping key value)

def PrimField.toField {base : RefTy} {p : PrimTy}
    (field : PrimField base p) : Field :=
  Field.primitive field.name (Ty.prim p)

mutual
  def Place.kind : Place kind ty -> Kind
    | .storageVar .. => Kind.storage
    | .memoryVar .. => Kind.memory
    | .stackVar .. => Kind.stack
    | .fieldRef (kind := kind) .. => kind
    | .fieldMap (kind := kind) .. => kind
    | .fieldPrim (kind := kind) .. => kind
    | .arrayIndex (kind := kind) .. => kind
    | .mappingIndex .. => Kind.storage

  def Expr.kind : Expr kind ty -> Kind
    | .place place => place.kind
    | .bool _ => Kind.stack
    | .call kind _ _ _ => kind
    | .and _ _ => Kind.stack

  def WrappedExpr.kind : WrappedExpr -> Kind
    | .var kind _ _ => kind
    | .field kind _ _ _ => kind
    | .index kind _ _ _ => kind
    | .pushPlace _ => Kind.storage
    | .bool _ => Kind.stack
    | .intLit _ _ => Kind.stack
    | .mkCall kind _ _ _ => kind
    | .mkBinop .. => Kind.stack
    | .mkUnop .. => Kind.stack
    | .mkIncDec .. => Kind.stack
    | .mkTernary .. => Kind.stack
end

mutual
  def Place.ty : Place kind ty -> Ty
    | .storageVar _ ref => Ty.ref ref
    | .memoryVar _ ref _ => Ty.ref ref
    | .stackVar _ ty _ => ty
    | .fieldRef (ref := ref) .. => Ty.ref ref
    | .fieldMap (key := key) (value := value) .. =>
        Ty.ref (RefTy.mapping key value)
    | .fieldPrim (p := p) .. => Ty.prim p
    | .arrayIndex (elem := elem) .. => elem
    | .mappingIndex (value := value) .. => value

  def Expr.ty : Expr kind ty -> Ty
    | .place place => place.ty
    | .bool _ => Ty.bool
    | .call _ ty _ _ => ty
    | .and _ _ => Ty.bool

  def WrappedExpr.ty : WrappedExpr -> Ty
    | .var _ ty _ => ty
    | .field _ ty _ _ => ty
    | .index _ ty _ _ => ty
    | .pushPlace target => Ty.indexElemTy target.ty
    | .bool _ => Ty.bool
    | .intLit ty _ => ty
    | .mkCall _ ty _ _ => ty
    | .mkBinop op lhs _ => op.retTy lhs.ty
    | .mkUnop op arg => op.retTy arg.ty
    | .mkIncDec _ target => target.ty
    | .mkTernary _ thn _ => thn.ty
end

mutual
  def Place.size : Place kind ty -> Nat
    | .storageVar .. => 1
    | .memoryVar .. => 1
    | .stackVar .. => 1
    | .fieldRef base _ => 1 + base.size
    | .fieldMap base _ => 1 + base.size
    | .fieldPrim base _ => 1 + base.size
    | .arrayIndex base index => 1 + base.size + index.size
    | .mappingIndex base key => 1 + base.size + key.size

  def Expr.size : Expr kind ty -> Nat
    | .place place => place.size
    | .bool _ => 1
    | .call _ _ _ args => 1 + WrappedExpr.sizeList args
    | .and lhs rhs => 1 + lhs.size + rhs.size

  def WrappedExpr.size : WrappedExpr -> Nat
    | .var .. => 1
    | .field _ _ base _ => 1 + base.size
    | .index _ _ base index => 1 + base.size + index.size
    | .pushPlace target => 3 + target.size
    | .bool _ => 1
    | .intLit _ _ => 1
    | .mkCall _ _ _ args => 1 + WrappedExpr.sizeList args
    | .mkBinop _ lhs rhs => 1 + lhs.size + rhs.size
    | .mkUnop _ arg => 1 + arg.size
    | .mkIncDec _ target => 4 + 2 * target.size
    | .mkTernary cond thn els => 1 + cond.size + thn.size + els.size

  def WrappedExpr.sizeList : List WrappedExpr -> Nat
    | [] => 0
    | expr :: rest => expr.size + WrappedExpr.sizeList rest
end

mutual
  def Place.complexCount : Place kind ty -> Nat
    | .storageVar .. => 0
    | .memoryVar .. => 0
    | .stackVar .. => 0
    | .fieldRef base _ => 1 + base.complexCount
    | .fieldMap base _ => 1 + base.complexCount
    | .fieldPrim base _ => 1 + base.complexCount
    | .arrayIndex base index => 1 + base.complexCount + index.complexCount
    | .mappingIndex base key => 1 + base.complexCount + key.complexCount

  def Expr.complexCount : Expr kind ty -> Nat
    | .place place => place.complexCount
    | .bool _ => 0
    | .call _ _ _ args => 1 + WrappedExpr.complexCountList args
    | .and lhs rhs => 1 + lhs.complexCount + rhs.complexCount

  def WrappedExpr.complexCount : WrappedExpr -> Nat
    | .var .. => 0
    | .field _ _ base _ => 1 + base.complexCount
    | .index _ _ base index => 1 + base.complexCount + index.complexCount
    | .pushPlace target => 2 + target.complexCount
    | .bool _ => 0
    | .intLit _ _ => 0
    | .mkCall _ _ _ args => 1 + WrappedExpr.complexCountList args
    | .mkBinop _ lhs rhs => 1 + lhs.complexCount + rhs.complexCount
    | .mkUnop _ arg => 1 + arg.complexCount
    | .mkIncDec _ target => 1 + target.complexCount
    | .mkTernary cond thn els =>
        1 + cond.complexCount + thn.complexCount + els.complexCount

  def WrappedExpr.complexCountList : List WrappedExpr -> Nat
    | [] => 0
    | expr :: rest => expr.complexCount + WrappedExpr.complexCountList rest
end

def Expr.simple : Expr k t -> Bool
  | .place (.storageVar ..) => true
  | .place (.memoryVar ..) => true
  | .place (.stackVar ..) => true
  | .bool _ => true
  | _ => false

def Expr.complex (expr : Expr k t) : Bool :=
  !expr.simple

def Expr.isComplex (expr : Expr k t) : Bool :=
  expr.complexCount != 0

namespace WrappedExpr

mutual
  def place {kind : Kind} {ty : Ty} : Place kind ty -> WrappedExpr
    | .storageVar name ref =>
        WrappedExpr.var Kind.storage (Ty.ref ref) (Field.identity name ref)
    | .memoryVar name ref _ =>
        WrappedExpr.var Kind.memory (Ty.ref ref) (Field.identity name ref)
    | .stackVar name ty _ =>
        WrappedExpr.var Kind.stack ty (Field.primitive name ty)
    | .fieldRef (ref := ref) base fld =>
        WrappedExpr.field base.kind (Ty.ref ref) (place base) fld.toField
    | .fieldMap (key := key) (value := value) base fld =>
        WrappedExpr.field base.kind (Ty.ref (RefTy.mapping key value))
          (place base) fld.toField
    | .fieldPrim (p := p) base fld =>
        WrappedExpr.field base.kind (Ty.prim p) (place base) fld.toField
    | .arrayIndex (elem := elem) base idx =>
        WrappedExpr.index base.kind elem (place base) (wrapExpr idx)
    | .mappingIndex (value := value) base key =>
        WrappedExpr.index Kind.storage value (place base) (wrapExpr key)

  def wrapExpr {kind : Kind} {ty : Ty} : Expr kind ty -> WrappedExpr
    | .place place => WrappedExpr.place place
    | .bool value => WrappedExpr.bool value
    | .call kind ty name args => WrappedExpr.mkCall kind ty name args
    | .and lhs rhs =>
        WrappedExpr.mkBinop BinOp.and (wrapExpr lhs) (wrapExpr rhs)
end

def wrap {kind : Kind} {ty : Ty} (expr : Expr kind ty) : WrappedExpr :=
  wrapExpr expr

def simple : WrappedExpr -> Bool
  | .var .. => true
  | .bool _ => true
  | .intLit _ _ => true
  | _ => false

def complex (expr : WrappedExpr) : Bool :=
  !expr.simple

def isComplex (expr : WrappedExpr) : Bool :=
  expr.complexCount != 0

def isSimpleAtom : WrappedExpr -> Bool
  | .var .. => true
  | .bool _ => true
  | .intLit _ _ => true
  | _ => false

def isStack (expr : WrappedExpr) : Bool :=
  expr.kind = Kind.stack

def isStorage (expr : WrappedExpr) : Bool :=
  expr.kind = Kind.storage

def isMemory (expr : WrappedExpr) : Bool :=
  expr.kind = Kind.memory

def isLocal : WrappedExpr -> Bool
  | .var Kind.storage _ fld => fld.origin = some StorageOrigin.local
  | _ => false

def isGlobal : WrappedExpr -> Bool
  | .var Kind.storage _ fld => fld.origin = some StorageOrigin.global
  | _ => false

def isPrimitive (expr : WrappedExpr) : Bool :=
  expr.ty.isPrimitive

def isIdentity (expr : WrappedExpr) : Bool :=
  expr.ty.isReference

def assignable : WrappedExpr -> Bool
  | .var .. => true
  | .field .. => true
  | .index .. => true
  | .pushPlace target => target.assignable
  | _ => false

end WrappedExpr

end Typed

export Typed (Expr Place WrappedExpr)

namespace WrappedExpr

abbrev wrap {kind : Kind} {ty : Ty} := @Typed.WrappedExpr.wrap kind ty
@[match_pattern] abbrev var := Typed.WrappedExpr.var
@[match_pattern] abbrev field := Typed.WrappedExpr.field
@[match_pattern] abbrev index := Typed.WrappedExpr.index
@[match_pattern] abbrev pushPlace := Typed.WrappedExpr.pushPlace
@[match_pattern] abbrev bool := Typed.WrappedExpr.bool
@[match_pattern] abbrev intLit := Typed.WrappedExpr.intLit
@[match_pattern] abbrev call := Typed.WrappedExpr.call
abbrev and := Typed.WrappedExpr.and
@[match_pattern] abbrev binop := Typed.WrappedExpr.mkBinop
@[match_pattern] abbrev unop := Typed.WrappedExpr.mkUnop
@[match_pattern] abbrev incDec := Typed.WrappedExpr.mkIncDec
@[match_pattern] abbrev ternary := Typed.WrappedExpr.mkTernary

def kind (expr : WrappedExpr) : Kind := Typed.WrappedExpr.kind expr
def ty (expr : WrappedExpr) : Ty := Typed.WrappedExpr.ty expr
def size (expr : WrappedExpr) : Nat := Typed.WrappedExpr.size expr
def sizeList (exprs : List WrappedExpr) : Nat := Typed.WrappedExpr.sizeList exprs
def complexCount (expr : WrappedExpr) : Nat := Typed.WrappedExpr.complexCount expr
def complexCountList (exprs : List WrappedExpr) : Nat :=
  Typed.WrappedExpr.complexCountList exprs
abbrev wrapExpr {kind : Kind} {ty : Ty} := @Typed.WrappedExpr.wrapExpr kind ty
abbrev place {kind : Kind} {ty : Ty} := @Typed.WrappedExpr.place kind ty
def simple (expr : WrappedExpr) : Bool := Typed.WrappedExpr.simple expr
def complex (expr : WrappedExpr) : Bool := Typed.WrappedExpr.complex expr
def isComplex (expr : WrappedExpr) : Bool := Typed.WrappedExpr.isComplex expr
def isSimpleAtom (expr : WrappedExpr) : Bool := Typed.WrappedExpr.isSimpleAtom expr
def isStack (expr : WrappedExpr) : Bool := Typed.WrappedExpr.isStack expr
def isStorage (expr : WrappedExpr) : Bool := Typed.WrappedExpr.isStorage expr
def isMemory (expr : WrappedExpr) : Bool := Typed.WrappedExpr.isMemory expr
def isLocal (expr : WrappedExpr) : Bool := Typed.WrappedExpr.isLocal expr
def isGlobal (expr : WrappedExpr) : Bool := Typed.WrappedExpr.isGlobal expr
def isPrimitive (expr : WrappedExpr) : Bool := Typed.WrappedExpr.isPrimitive expr
def isIdentity (expr : WrappedExpr) : Bool := Typed.WrappedExpr.isIdentity expr
def assignable (expr : WrappedExpr) : Bool := Typed.WrappedExpr.assignable expr

end WrappedExpr

structure PlaceExpr where
  expr : WrappedExpr
  assignable : expr.assignable = true

instance : Repr PlaceExpr where
  reprPrec place prec := reprPrec place.expr prec

namespace PlaceExpr

instance : Coe PlaceExpr WrappedExpr where
  coe place := place.expr

def var (kind : Kind) (ty : Ty) (field : Field) : PlaceExpr :=
  ⟨WrappedExpr.var kind ty field, rfl⟩

def field (kind : Kind) (ty : Ty) (base : WrappedExpr) (field : Field) :
    PlaceExpr :=
  ⟨WrappedExpr.field kind ty base field, rfl⟩

def index (kind : Kind) (ty : Ty) (base index : WrappedExpr) : PlaceExpr :=
  ⟨WrappedExpr.index kind ty base index, rfl⟩

def pushPlace (target : PlaceExpr) : PlaceExpr :=
  ⟨WrappedExpr.pushPlace target, target.assignable⟩

def kind (place : PlaceExpr) : Kind :=
  place.expr.kind

def ty (place : PlaceExpr) : Ty :=
  place.expr.ty

def size (place : PlaceExpr) : Nat :=
  place.expr.size

def complexCount (place : PlaceExpr) : Nat :=
  place.expr.complexCount

def ofWrappedVar (kind : Kind) (ty : Ty) (field : Field) : PlaceExpr :=
  var kind ty field

def ofWrappedField
    (kind : Kind) (ty : Ty) (base : WrappedExpr) (fld : Field) :
    PlaceExpr :=
  PlaceExpr.field kind ty base fld

def ofWrappedIndex
    (kind : Kind) (ty : Ty) (base idx : WrappedExpr) : PlaceExpr :=
  PlaceExpr.index kind ty base idx

def ofWrappedPushPlace (target : PlaceExpr) : PlaceExpr :=
  PlaceExpr.pushPlace target

end PlaceExpr

namespace StandardExample

def personRef : RefTy := RefTy.struct "Person"
def accountRef : RefTy := RefTy.struct "Account"
def tokenRef : RefTy := RefTy.struct "Token"

def personTy : Ty := Ty.ref personRef
def accountTy : Ty := Ty.ref accountRef
def tokenTy : Ty := Ty.ref tokenRef

def accountField : Field := Field.identity "account" accountRef
def tokenField : Field := Field.identity "token" tokenRef
def ageField : Field := Field.primitive "age" Ty.uint
def balanceField : Field := Field.primitive "balance" Ty.int
def valueField : Field := Field.primitive "value" Ty.uint

def storagePerson (name : Name) : WrappedExpr :=
  WrappedExpr.var Kind.storage personTy
    (Field.identity name personRef (some StorageOrigin.global))

def storagePersonPlace (name : Name) : PlaceExpr :=
  PlaceExpr.var Kind.storage personTy
    (Field.identity name personRef (some StorageOrigin.global))

def memoryPerson (name : Name) : WrappedExpr :=
  WrappedExpr.var Kind.memory personTy (Field.identity name personRef)

def memoryPersonPlace (name : Name) : PlaceExpr :=
  PlaceExpr.var Kind.memory personTy (Field.identity name personRef)

def stackBool (name : Name) : WrappedExpr :=
  WrappedExpr.var Kind.stack Ty.bool (Field.primitive name Ty.bool)

def stackBoolPlace (name : Name) : PlaceExpr :=
  PlaceExpr.var Kind.stack Ty.bool (Field.primitive name Ty.bool)

def stackUint (name : Name) : WrappedExpr :=
  WrappedExpr.var Kind.stack Ty.uint (Field.primitive name Ty.uint)

def stackUintPlace (name : Name) : PlaceExpr :=
  PlaceExpr.var Kind.stack Ty.uint (Field.primitive name Ty.uint)

def stackInt (name : Name) : WrappedExpr :=
  WrappedExpr.var Kind.stack Ty.int (Field.primitive name Ty.int)

def stackIntPlace (name : Name) : PlaceExpr :=
  PlaceExpr.var Kind.stack Ty.int (Field.primitive name Ty.int)

def accountOf (kind : Kind) (person : WrappedExpr) : WrappedExpr :=
  WrappedExpr.field kind accountTy person accountField

def accountPlaceOf (kind : Kind) (person : WrappedExpr) : PlaceExpr :=
  PlaceExpr.field kind accountTy person accountField

def tokenOf (kind : Kind) (account : WrappedExpr) : WrappedExpr :=
  WrappedExpr.field kind tokenTy account tokenField

def tokenPlaceOf (kind : Kind) (account : WrappedExpr) : PlaceExpr :=
  PlaceExpr.field kind tokenTy account tokenField

def ageOf (kind : Kind) (person : WrappedExpr) : WrappedExpr :=
  WrappedExpr.field kind Ty.uint person ageField

def agePlaceOf (kind : Kind) (person : WrappedExpr) : PlaceExpr :=
  PlaceExpr.field kind Ty.uint person ageField

def balanceOf (kind : Kind) (account : WrappedExpr) : WrappedExpr :=
  WrappedExpr.field kind Ty.int account balanceField

def balancePlaceOf (kind : Kind) (account : WrappedExpr) : PlaceExpr :=
  PlaceExpr.field kind Ty.int account balanceField

def valueOf (kind : Kind) (token : WrappedExpr) : WrappedExpr :=
  WrappedExpr.field kind Ty.uint token valueField

def valuePlaceOf (kind : Kind) (token : WrappedExpr) : PlaceExpr :=
  PlaceExpr.field kind Ty.uint token valueField

end StandardExample

inductive Stmt where
  | expr (expr : WrappedExpr)
  | assign (lhs : PlaceExpr) (rhs : WrappedExpr)
  | storageDecl (ty : Ty) (name : Name) (init : Option WrappedExpr)
  | storagePlaceAlias (ty : Ty) (name : Name) (init : WrappedExpr)
  | memoryDecl (ty : Ty) (name : Name) (init : Option WrappedExpr)
  | stackDecl (ty : Ty) (name : Name) (init : Option WrappedExpr)
  | delete (target : PlaceExpr)
  | push (target : PlaceExpr) (value : Option WrappedExpr)
  | pushAssign (target : PlaceExpr) (value : WrappedExpr)
  | pushFieldAssign (target : PlaceExpr) (field : Field) (value : WrappedExpr)
  | pop (target : PlaceExpr)
  | revert (message : Option WrappedExpr)
  /-- `lhs op= rhs;` — KeY `storage{Root,Field,Index}{Add,..,Mod}Assign`. -/
  | compoundAssign (op : BinOp) (lhs : PlaceExpr) (rhs : WrappedExpr)
  /-- `if (cond) { thn } else { els }` — KeY `ifThenElseRules.key`. -/
  | ite (cond : WrappedExpr) (thn els : List Stmt)
  /-- `assert(cond);` — KeY `assertConditionCapture`/`assertSimple`. -/
  | assertStmt (cond : WrappedExpr)
  /-- `require(cond);` — KeY `requireConditionCapture`/`requireSimple`. -/
  | requireStmt (cond : WrappedExpr)
  /-- `recipient.transfer(amount);` — KeY `transfer*` taclets. -/
  | transfer (recipient amount : WrappedExpr)
  /-- `result = f(args);` (or bare `f(args);`) — KeY
  `FunctionBodyStatement`, consumed by `functionBodyExpand`. The
  interpreter is stuck on it; meaning comes from inlining
  (`SoliditySyntax.inlineBlock`, `SolidityJudgment.checkInlined`). -/
  | callStmt (result : Option PlaceExpr) (fn : Name) (args : List WrappedExpr)
  deriving Repr

abbrev Block := List Stmt

namespace ValidSyntax

def IsStorageArrayPlace (target : WrappedExpr) : Prop :=
  target.assignable = true ∧ target.kind = Kind.storage ∧
    ∃ elem, target.ty = Ty.ref (RefTy.array elem)

def IsIndexExpr (expr : WrappedExpr) : Prop :=
  expr.kind = Kind.stack ∧ expr.ty = Ty.uint

def ArrayElemTy (target : WrappedExpr) (elem : Ty) : Prop :=
  target.ty = Ty.ref (RefTy.array elem)

end ValidSyntax

namespace SoliditySyntax

def fieldFor (name : Name) (ty : Ty)
    (origin : Option StorageOrigin := none) : Field :=
  match ty with
  | Ty.ref ref => Field.identity name ref origin
  | _ => Field.primitive name ty origin

def storageOriginFor (name : Name) : Option StorageOrigin :=
  match name with
  | "alice" | "bob" | "people" => some StorageOrigin.global
  -- StandardExample.sol globals (keyext.solidity.examples/taclets).
  | "total" | "age" | "owner" | "balance" | "values" | "balances"
  | "flags" | "folks" | "matrix" | "persons" | "wallet" =>
      some StorageOrigin.global
  | "p" | "acc" | "sp" | "src" | "tgt" | "pv" | "pp" | "bp"
  | "aliceAlias" | "tokRef" | "aliceAcc" | "aliceTok" | "m" =>
      some StorageOrigin.local
  | _ => none

def localStorageTyFor (name : Name) : Ty :=
  match name with
  | "acc" | "bp" | "aliceAcc" | "sp" => StandardExample.accountTy
  | "tokRef" | "aliceTok" => StandardExample.tokenTy
  | "m" => Ty.ref (RefTy.array (Ty.ref (RefTy.array Ty.uint)))
  | "src" | "tgt" | "pv" | "pp" =>
      StandardExample.personTy
  | _ => StandardExample.personTy

def originFor (kind : Kind) (name : Name) : Option StorageOrigin :=
  match kind with
  | Kind.storage => storageOriginFor name
  | _ => none

def varExpr (kind : Kind) (ty : Ty) (name : Name) : WrappedExpr :=
  WrappedExpr.var kind ty (fieldFor name ty (originFor kind name))

def varPlace (kind : Kind) (ty : Ty) (name : Name) : PlaceExpr :=
  PlaceExpr.var kind ty (fieldFor name ty (originFor kind name))

def rootExpr (name : Name) : WrappedExpr :=
  match name with
  | "true" => WrappedExpr.bool true
  | "false" => WrappedExpr.bool false
  | "alice" => varExpr Kind.storage StandardExample.personTy "alice"
  | "bob" => varExpr Kind.storage StandardExample.personTy "bob"
  | "carol" => StandardExample.memoryPerson "carol"
  | "david" => StandardExample.memoryPerson "david"
  | "mv" => varExpr Kind.memory StandardExample.accountTy "mv"
  | "flag" => StandardExample.stackBool "flag"
  | "i" => StandardExample.stackUint "i"
  | "amount" => StandardExample.stackUint "amount"
  -- Explicit arms for common stack names: same value as the default arm,
  -- but the listed arm keeps skip-condition goals reducible for `decide`.
  | "result" | "x" | "y" | "to" | "rv" | "idx" => StandardExample.stackUint name
  | "people" =>
      varExpr Kind.storage (Ty.ref (RefTy.array StandardExample.personTy))
        "people"
  -- StandardExample.sol globals (keyext.solidity.examples/taclets).
  | "total" | "age" | "balance" | "owner" =>
      varExpr Kind.storage Ty.uint name
  | "values" =>
      varExpr Kind.storage (Ty.ref (RefTy.array Ty.uint)) name
  | "balances" =>
      varExpr Kind.storage (Ty.ref (RefTy.mapping Ty.uint Ty.uint)) name
  | "flags" =>
      varExpr Kind.storage (Ty.ref (RefTy.mapping Ty.uint Ty.bool)) name
  | "folks" =>
      varExpr Kind.storage
        (Ty.ref (RefTy.mapping Ty.uint StandardExample.personTy)) name
  | "matrix" =>
      varExpr Kind.storage
        (Ty.ref (RefTy.array (Ty.ref (RefTy.array Ty.uint)))) name
  | "persons" =>
      varExpr Kind.storage (Ty.ref (RefTy.array StandardExample.personTy))
        name
  | "wallet" =>
      varExpr Kind.storage (Ty.ref (RefTy.struct "Wallet")) name
  | "p" | "acc" | "sp" | "src" | "tgt" | "pv" | "pp" | "bp"
  | "aliceAlias" | "tokRef" | "aliceAcc" | "aliceTok" | "m" =>
      varExpr Kind.storage (localStorageTyFor name) name
  | _ => StandardExample.stackUint name

def rootPlace (name : Name) : PlaceExpr :=
  match name with
  | "alice" => varPlace Kind.storage StandardExample.personTy "alice"
  | "bob" => varPlace Kind.storage StandardExample.personTy "bob"
  | "carol" => StandardExample.memoryPersonPlace "carol"
  | "david" => StandardExample.memoryPersonPlace "david"
  | "mv" => varPlace Kind.memory StandardExample.accountTy "mv"
  | "flag" => StandardExample.stackBoolPlace "flag"
  | "i" => StandardExample.stackUintPlace "i"
  | "amount" => StandardExample.stackUintPlace "amount"
  -- Explicit arms for common stack names (see `rootExpr`).
  | "result" | "x" | "y" | "to" | "rv" | "idx" =>
      StandardExample.stackUintPlace name
  | "people" =>
      varPlace Kind.storage (Ty.ref (RefTy.array StandardExample.personTy))
        "people"
  -- StandardExample.sol globals (keyext.solidity.examples/taclets).
  | "total" | "age" | "balance" | "owner" =>
      varPlace Kind.storage Ty.uint name
  | "values" =>
      varPlace Kind.storage (Ty.ref (RefTy.array Ty.uint)) name
  | "balances" =>
      varPlace Kind.storage (Ty.ref (RefTy.mapping Ty.uint Ty.uint)) name
  | "flags" =>
      varPlace Kind.storage (Ty.ref (RefTy.mapping Ty.uint Ty.bool)) name
  | "folks" =>
      varPlace Kind.storage
        (Ty.ref (RefTy.mapping Ty.uint StandardExample.personTy)) name
  | "matrix" =>
      varPlace Kind.storage
        (Ty.ref (RefTy.array (Ty.ref (RefTy.array Ty.uint)))) name
  | "persons" =>
      varPlace Kind.storage (Ty.ref (RefTy.array StandardExample.personTy))
        name
  | "wallet" =>
      varPlace Kind.storage (Ty.ref (RefTy.struct "Wallet")) name
  | "p" | "acc" | "sp" | "src" | "tgt" | "pv" | "pp" | "bp"
  | "aliceAlias" | "tokRef" | "aliceAcc" | "aliceTok" | "m" =>
      varPlace Kind.storage (localStorageTyFor name) name
  | _ => StandardExample.stackUintPlace name

def fieldTy (name : Name) : Ty :=
  match name with
  | "account" => StandardExample.accountTy
  | "token" => StandardExample.tokenTy
  | "age" => Ty.uint
  | "balance" => Ty.int
  | "value" => Ty.uint
  | "friends" => Ty.ref (RefTy.array StandardExample.personTy)
  | "stash" => Ty.ref (RefTy.mapping Ty.uint Ty.uint)
  -- `Ledger.balances`, the mapping member the calculus's struct-delete
  -- example turns on: `delete` resets the struct and keeps the mapping.
  | "balances" => Ty.ref (RefTy.mapping Ty.uint Ty.uint)
  | "length" => Ty.uint
  -- Reference-typed members of the ported solkey contracts' structs. The
  -- `uint` members (`a`, `b`, `c`, `x`, `y`, `z`, `n`, `nonce`, `value`)
  -- need no arm: they take the `uint` default. `fieldForName` derives the
  -- `Field` from this type, so extending it here is enough.
  | "items" => Ty.ref (RefTy.array Ty.uint)
  -- The calculus's auxiliary array members (`alice.accounts`,
  -- `carol.account.values` are `uint[]`; `alice.account.tokens` is
  -- `Token[]`, below), used by its storage- and memory-array examples.
  | "accounts" | "values" => Ty.ref (RefTy.array Ty.uint)
  | "ledger" => Ty.ref (RefTy.struct "Ledger")
  | "tokens" => Ty.ref (RefTy.array StandardExample.tokenTy)
  | "sub" => Ty.ref (RefTy.struct "Sub")
  | "inner" => Ty.ref (RefTy.struct "Inner")
  -- `Toggle.on`; its `n` member takes the `uint` default, as `WithArray.n`
  -- already does.
  | "on" => Ty.bool
  | _ => Ty.uint

def fieldForName (name : Name) : Field :=
  match name with
  | "account" => StandardExample.accountField
  | "token" => StandardExample.tokenField
  | "age" => StandardExample.ageField
  | "balance" => StandardExample.balanceField
  | "value" => StandardExample.valueField
  | "friends" => Field.identity "friends" (RefTy.array StandardExample.personTy)
  | _ => fieldFor name (fieldTy name)

def fieldExpr (base : WrappedExpr) (name : Name) : WrappedExpr :=
  WrappedExpr.field base.kind (fieldTy name) base (fieldForName name)

def fieldPlace (base : WrappedExpr) (name : Name) : PlaceExpr :=
  PlaceExpr.field base.kind (fieldTy name) base (fieldForName name)

def indexElemTy : Ty -> Ty :=
  Ty.indexElemTy

def indexExpr (base index : WrappedExpr) : WrappedExpr :=
  WrappedExpr.index base.kind (indexElemTy base.ty) base index

def indexPlace (base index : WrappedExpr) : PlaceExpr :=
  PlaceExpr.index base.kind (indexElemTy base.ty) base index

def pushPlaceExpr (target : PlaceExpr) : WrappedExpr :=
  WrappedExpr.pushPlace target

def pushPlace (target : PlaceExpr) : PlaceExpr :=
  PlaceExpr.pushPlace target

def stackCallExpr (ty : Ty) (name : Name) (args : List WrappedExpr)
    (primitive : ty.isPrimitive = true) : WrappedExpr :=
  WrappedExpr.call Kind.stack ty name args (ok := by
    simp [ExprCallOk, primitive])

def memoryCallExpr (ref : RefTy) (name : Name) (args : List WrappedExpr)
    (allows : ref.allowsMemory = true) : WrappedExpr :=
  WrappedExpr.call Kind.memory (Ty.ref ref) name args (ok := by
    constructor
    · intro h
      cases h
    · constructor
      · intro h
        cases h
      · intro _h
        simp [Ty.isReference, Ty.isPrimitive, Ty.allowsMemory, allows])

def callExpr (name : Name) (args : List WrappedExpr) : WrappedExpr :=
  stackCallExpr Ty.uint name args rfl

def andExpr (lhs rhs : WrappedExpr) : WrappedExpr :=
  Typed.WrappedExpr.mkBinop BinOp.and lhs rhs

def intLitExpr (value : Int) (ty : Ty := Ty.uint) : WrappedExpr :=
  WrappedExpr.intLit ty value

def binopExpr (op : BinOp) (lhs rhs : WrappedExpr) : WrappedExpr :=
  Typed.WrappedExpr.mkBinop op lhs rhs

def unopExpr (op : UnOp) (arg : WrappedExpr) : WrappedExpr :=
  Typed.WrappedExpr.mkUnop op arg

def incDecExpr (op : IncDec) (target : WrappedExpr) : WrappedExpr :=
  Typed.WrappedExpr.mkIncDec op target

def ternaryExpr (cond thn els : WrappedExpr) : WrappedExpr :=
  Typed.WrappedExpr.mkTernary cond thn els

def typedVarTy (name : Name) : Ty :=
  match name with
  | "Person" => StandardExample.personTy
  | "Account" => StandardExample.accountTy
  | "Token" => StandardExample.tokenTy
  | "PersonArray" => Ty.ref (RefTy.array StandardExample.personTy)
  | "UintMatrix" => Ty.ref (RefTy.array (Ty.ref (RefTy.array Ty.uint)))
  -- Struct types of the ported solkey contracts.
  | "Basket" | "Ledger" | "LedgerUse" | "TokenBucket" | "Toggle" | "Pair"
  | "S" | "Sub" | "WithSub" | "Inner" | "Outer" | "Simple" | "WithArray"
  | "Triple" => Ty.ref (RefTy.struct name)
  -- Reference types with no single-ident Solidity spelling.
  | "UintArray" => Ty.ref (RefTy.array Ty.uint)
  | "BoolArray" => Ty.ref (RefTy.array Ty.bool)
  | "TokenArray" => Ty.ref (RefTy.array StandardExample.tokenTy)
  | "TokenBucketArray" =>
      Ty.ref (RefTy.array (Ty.ref (RefTy.struct "TokenBucket")))
  | "PairArray" => Ty.ref (RefTy.array (Ty.ref (RefTy.struct "Pair")))
  | "InnerArray" => Ty.ref (RefTy.array (Ty.ref (RefTy.struct "Inner")))
  | "LedgerUseArray" =>
      Ty.ref (RefTy.array (Ty.ref (RefTy.struct "LedgerUse")))
  | "UintMap" => Ty.ref (RefTy.mapping Ty.uint Ty.uint)
  | "UintArrayMap" =>
      Ty.ref (RefTy.mapping Ty.uint (Ty.ref (RefTy.array Ty.uint)))
  | "AccountMap" =>
      Ty.ref (RefTy.mapping Ty.uint StandardExample.accountTy)
  | "SMap" => Ty.ref (RefTy.mapping Ty.uint (Ty.ref (RefTy.struct "S")))
  | "WithSubMap" =>
      Ty.ref (RefTy.mapping Ty.uint (Ty.ref (RefTy.struct "WithSub")))
  | "SimpleMap" =>
      Ty.ref (RefTy.mapping Ty.uint (Ty.ref (RefTy.struct "Simple")))
  | "bool" => Ty.bool
  | "uint" => Ty.uint
  | "int" => Ty.int
  | _ => Ty.uint

def typedKind (name : Name) : Kind :=
  match name with
  | "storage" => Kind.storage
  | "memory" => Kind.memory
  | "stack" => Kind.stack
  | _ => Kind.stack

def declTy (name : Name) : Ty :=
  typedVarTy name

/-- Infer the Kind from an alias variable name.
    - "sp" → Kind.storage (storage path alias)
    - "mv" → Kind.memory (memory path alias)
    - "pv" → Kind.memory (value alias, typically memory)
    - "idx" → Kind.stack (index alias)

    This is a name-only table; a `pv`/`rv`/`idx` alias at a *primitive* type is
    a stack value, which the `sol_expr` expanders handle through
    `isStackScratchAlias` rather than here. -/
def aliasKind (name : Name) : Kind :=
  match name with
  | "sp" => Kind.storage
  | "mv" => Kind.memory
  | "pv" => Kind.memory
  | "idx" => Kind.stack
  -- The same solkey name is a `storage` alias in one function and a
  -- `memory` alias in another (`Account storage acc` in
  -- `storageAliasWrite`, `Account memory acc` in `memoryFieldAlias`), so
  -- a name->kind table cannot serve both. The port renames every *memory*
  -- alias to one of these; storage aliases keep their solkey name.
  | "mv2" | "mv3" | "mv4" => Kind.memory
  | _ => Kind.storage  -- default to storage for unknown aliases

/-- Build an alias expression with inferred kind -/
def aliasExpr (name : Name) (ty : Ty) : WrappedExpr :=
  let kind := aliasKind name
  let origin : Option StorageOrigin :=
    match kind with
    | Kind.storage => some StorageOrigin.local
    | _ => none
  WrappedExpr.var kind ty (fieldFor name ty origin)

/-- A *state variable* of a ported solkey contract, written `name@@Type`.

This deliberately does not go through `rootExpr`/`storageOriginFor`.
Those are matches on the variable name, and every `sol!` judgment pays
for their size: widening them with the state variables of seven more
contracts roughly doubled the cost of elaborating *any* judgment, which
was enough to exhaust the `whnf` budget on proofs that had been passing.
Carrying the type at the use site keeps the ported contracts' schemas out
of those tables entirely, so the cost is independent of how many
contracts are ported. `StorageOrigin.global` is what makes `resolveS`
treat the name as a storage root rather than requiring an `env` binding. -/
def globalExpr (name : Name) (ty : Ty) : WrappedExpr :=
  WrappedExpr.var Kind.storage ty
    (fieldFor name ty (some StorageOrigin.global))

/-- The place counterpart of `globalExpr`. -/
def globalPlace (name : Name) (ty : Ty) : PlaceExpr :=
  PlaceExpr.var Kind.storage ty
    (fieldFor name ty (some StorageOrigin.global))

/-- Build an alias place with inferred kind -/
def aliasPlace (name : Name) (ty : Ty) : PlaceExpr :=
  let kind := aliasKind name
  let origin : Option StorageOrigin :=
    match kind with
    | Kind.storage => some StorageOrigin.local
    | _ => none
  PlaceExpr.var kind ty (fieldFor name ty origin)

end SoliditySyntax

open Lean Macro

declare_syntax_cat sol_expr
syntax ident : sol_expr
syntax num : sol_expr
syntax ident "(" sepBy(sol_expr, ", ") ")" : sol_expr
syntax ident "(" ")" "." ident : sol_expr
syntax sol_expr "." ident : sol_expr
syntax sol_expr "[" sol_expr "]" : sol_expr
syntax sol_expr ".push()" : sol_expr
-- Typed alias: sp@Account, sp@Account.balance, sp@PersonArray (dot splits type.field)
syntax ident "@" ident : sol_expr
-- State variable of a ported solkey contract: `age@@uint`, `alice@@Person`,
-- `withSubMap@@WithSubMap.sub.x`. See `SoliditySyntax.globalExpr`.
syntax ident "@@" ident : sol_expr
-- Parenthesized grouping.
syntax "(" sol_expr ")" : sol_expr
-- Binary operators, Solidity precedences. Comparisons and (in)equality exist
-- only in parenthesized form `(a < b)`: a bare trailing `<`/`>` operator
-- would swallow the closing `>` of the `sol!{ < stmts > (post) }` modality
-- syntax under longest-match parsing.
syntax:75 sol_expr:76 " ** " sol_expr:75 : sol_expr
syntax:70 sol_expr:70 " * " sol_expr:71 : sol_expr
syntax:70 sol_expr:70 " / " sol_expr:71 : sol_expr
syntax:70 sol_expr:70 " % " sol_expr:71 : sol_expr
syntax:65 sol_expr:65 " + " sol_expr:66 : sol_expr
syntax:65 sol_expr:65 " - " sol_expr:66 : sol_expr
syntax:35 sol_expr:36 " && " sol_expr:35 : sol_expr
syntax:30 sol_expr:31 " || " sol_expr:30 : sol_expr
syntax "(" sol_expr " < " sol_expr ")" : sol_expr
syntax "(" sol_expr " > " sol_expr ")" : sol_expr
syntax "(" sol_expr " <= " sol_expr ")" : sol_expr
syntax "(" sol_expr " >= " sol_expr ")" : sol_expr
syntax "(" sol_expr " == " sol_expr ")" : sol_expr
syntax "(" sol_expr " != " sol_expr ")" : sol_expr
-- Unary operators. `--` cannot be a token (it opens a Lean comment), so
-- decrements are spelled `predec(e)` / `postdec(e)`, standing for `--e`
-- and `e--`; without them the whole `{pre,post}decrement` taclet family
-- is unwritable in surface syntax and so unreachable from a port.
syntax:80 "!" sol_expr:80 : sol_expr
syntax:80 "-" sol_expr:80 : sol_expr
syntax:80 "++" sol_expr:80 : sol_expr
syntax:90 sol_expr:90 "++" : sol_expr
syntax:80 "predec" "(" sol_expr ")" : sol_expr
syntax:90 "postdec" "(" sol_expr ")" : sol_expr
-- Ternary `c ? t : e` (KeY `ternaryCaptureCond`/`ternaryToIf`), lowest
-- precedence, right-associative.
syntax:20 sol_expr:21 " ? " sol_expr:21 " : " sol_expr:20 : sol_expr

syntax "sexpr!" "{" sol_expr "}" : term
syntax "splace!" "{" sol_expr "}" : term
syntax "svar!" "{" ident ident ident "}" : term
syntax "sfield!" "{" ident ident ident "}" : term

declare_syntax_cat sol_stmt
syntax sol_expr "=" sol_expr : sol_stmt
syntax ident ident ident "=" sol_expr : sol_stmt
syntax ident ident ident : sol_stmt
syntax ident ident "=" sol_expr : sol_stmt
syntax ident ident : sol_stmt
syntax "delete " sol_expr : sol_stmt
syntax ident ".push()" "=" sol_expr : sol_stmt
syntax ident ".push()" "." ident "=" sol_expr : sol_stmt
syntax sol_expr ".push()" "=" sol_expr : sol_stmt
syntax sol_expr ".push()" "." ident "=" sol_expr : sol_stmt
syntax sol_expr ".push(" sol_expr ")" : sol_stmt
syntax sol_expr ".push()" : sol_stmt
syntax sol_expr ".pop()" : sol_stmt
syntax sol_expr " += " sol_expr : sol_stmt
syntax sol_expr " -= " sol_expr : sol_stmt
syntax sol_expr " *= " sol_expr : sol_stmt
syntax sol_expr " /= " sol_expr : sol_stmt
syntax sol_expr " %= " sol_expr : sol_stmt
syntax "assert" "(" sol_expr ")" : sol_stmt
syntax "require" "(" sol_expr ")" : sol_stmt
syntax "revert" "(" ")" : sol_stmt
syntax "if" "(" sol_expr ")" "{" sepBy(sol_stmt, ";", ";") "}"
  "else" "{" sepBy(sol_stmt, ";", ";") "}" : sol_stmt
syntax "if" "(" sol_expr ")" "{" sepBy(sol_stmt, ";", ";") "}" : sol_stmt
syntax sol_expr ".transfer(" sol_expr ")" : sol_stmt
syntax sol_expr : sol_stmt
-- Trailing context splice: `solbox!{ p.x = 1; .. rest }` is the block
-- `[p.x = 1] ++ rest`, the calculus's `<[ pi s omega ]>` with `omega` named
-- instead of retyped on every line of a derivation (`macros.sty`'s
-- `\ctxStmt`).  Only meaningful as the *last* element, and only to the block
-- macros -- `sstmt!` rejects it, since it denotes a `Block`, not a `Stmt`.
syntax ".. " ident : sol_stmt

syntax "sstmt!" "{" sol_stmt "}" : term

partial def expandSolPathExpr (parts : List String) : MacroM (TSyntax `term) := do
  match parts with
  | [] => Macro.throwError "empty Solidity expression"
  | root :: fields =>
      let mut acc ← `(SoliditySyntax.rootExpr $(quote root))
      for field in fields do
        acc ← `(SoliditySyntax.fieldExpr $acc $(quote field))
      pure acc

partial def expandSolPathPlace (parts : List String) : MacroM (TSyntax `term) := do
  match parts with
  | [] => Macro.throwError "empty Solidity place"
  | [root] => `(SoliditySyntax.rootPlace $(quote root))
  | root :: fields =>
      let mut acc ← `(SoliditySyntax.rootExpr $(quote root))
      for field in fields.dropLast do
        acc ← `(SoliditySyntax.fieldExpr $acc $(quote field))
      match fields.getLast? with
      | none => Macro.throwError "empty Solidity field path"
      | some field =>
          `(SoliditySyntax.fieldPlace $acc $(quote field))

/-- The scratch value aliases that the capture rules bind on the **stack**
(`Rules.valueAliasName` `pv`, `rhsValueAliasName` `rv`, `indexAliasName`
`idx`), as opposed to the storage/memory *path* aliases `sp`/`mv`.

`SoliditySyntax.aliasKind` maps a name to a kind without seeing the type, so
`pv@uint` would come out as a `memory` variable while
`Rules.captureStackValue`/`stackValueAlias` bind it on the stack (and
`Rules.valueCaptureKind` promotes a primitive memory capture to the stack).
The `sol_expr` expanders consult this table instead, deciding the kind at the
use site -- the same reasoning as the `name@@Type` globals, and for the same
reason: widening `aliasKind` itself would put an `if ty.isPrimitive` in front
of every `sp@...` occurrence in the corpus. -/
def isStackScratchAlias (name ty : String) : Bool :=
  (name == "pv" || name == "rv" || name == "idx") &&
    (ty == "uint" || ty == "int" || ty == "bool")

mutual
partial def expandSolBinop (op : BinOp) (lhs rhs : TSyntax `sol_expr) :
    MacroM (TSyntax `term) := do
  let lhsTerm ← expandSolExpr lhs
  let rhsTerm ← expandSolExpr rhs
  let opTerm ←
    match op with
    | .add => `(BinOp.add)
    | .sub => `(BinOp.sub)
    | .mul => `(BinOp.mul)
    | .pow => `(BinOp.pow)
    | .div => `(BinOp.div)
    | .mod => `(BinOp.mod)
    | .lt => `(BinOp.lt)
    | .gt => `(BinOp.gt)
    | .le => `(BinOp.le)
    | .ge => `(BinOp.ge)
    | .eqB => `(BinOp.eqB)
    | .neB => `(BinOp.neB)
    | .and => `(BinOp.and)
    | .or => `(BinOp.or)
  `(SoliditySyntax.binopExpr $opTerm $lhsTerm $rhsTerm)

partial def expandSolExpr : TSyntax `sol_expr -> MacroM (TSyntax `term)
  | `(sol_expr| $name:ident) =>
      expandSolPathExpr (name.getId.components.map Lean.Name.toString)
  | `(sol_expr| $fnName:ident($args,*)) => do
      let parts := fnName.getId.components.map Lean.Name.toString
      match parts.reverse with
      | "push" :: targetRev =>
          if args.getElems.isEmpty && !targetRev.isEmpty then do
            let targetTerm ← expandSolPathPlace targetRev.reverse
            `(SoliditySyntax.pushPlaceExpr $targetTerm)
          else do
            let expandedArgs ← args.getElems.mapM expandSolExpr
            `(SoliditySyntax.callExpr $(quote fnName.getId.toString)
                [$expandedArgs,*])
      | _ => do
          let expandedArgs ← args.getElems.mapM expandSolExpr
          `(SoliditySyntax.callExpr $(quote fnName.getId.toString)
              [$expandedArgs,*])
  | `(sol_expr| $base:sol_expr . $field:ident) => do
      let baseTerm ← expandSolExpr base
      `(SoliditySyntax.fieldExpr $baseTerm $(quote field.getId.toString))
  | `(sol_expr| $base:sol_expr[$index:sol_expr]) => do
      let baseTerm ← expandSolExpr base
      let indexTerm ← expandSolExpr index
      `(SoliditySyntax.indexExpr $baseTerm $indexTerm)
  | `(sol_expr| $base:sol_expr .push()) => do
      let baseTerm ← expandSolPlace base
      `(SoliditySyntax.pushPlaceExpr $baseTerm)
  | `(sol_expr| $n:num) =>
      `(SoliditySyntax.intLitExpr $(quote n.getNat))
  | `(sol_expr| ( $e:sol_expr )) => expandSolExpr e
  | `(sol_expr| $lhs:sol_expr ** $rhs:sol_expr) =>
      expandSolBinop BinOp.pow lhs rhs
  | `(sol_expr| $lhs:sol_expr * $rhs:sol_expr) =>
      expandSolBinop BinOp.mul lhs rhs
  | `(sol_expr| $lhs:sol_expr / $rhs:sol_expr) =>
      expandSolBinop BinOp.div lhs rhs
  | `(sol_expr| $lhs:sol_expr % $rhs:sol_expr) =>
      expandSolBinop BinOp.mod lhs rhs
  | `(sol_expr| $lhs:sol_expr + $rhs:sol_expr) =>
      expandSolBinop BinOp.add lhs rhs
  | `(sol_expr| $lhs:sol_expr - $rhs:sol_expr) =>
      expandSolBinop BinOp.sub lhs rhs
  | `(sol_expr| $lhs:sol_expr && $rhs:sol_expr) =>
      expandSolBinop BinOp.and lhs rhs
  | `(sol_expr| $lhs:sol_expr || $rhs:sol_expr) =>
      expandSolBinop BinOp.or lhs rhs
  | `(sol_expr| ( $lhs:sol_expr < $rhs:sol_expr )) =>
      expandSolBinop BinOp.lt lhs rhs
  | `(sol_expr| ( $lhs:sol_expr > $rhs:sol_expr )) =>
      expandSolBinop BinOp.gt lhs rhs
  | `(sol_expr| ( $lhs:sol_expr <= $rhs:sol_expr )) =>
      expandSolBinop BinOp.le lhs rhs
  | `(sol_expr| ( $lhs:sol_expr >= $rhs:sol_expr )) =>
      expandSolBinop BinOp.ge lhs rhs
  | `(sol_expr| ( $lhs:sol_expr == $rhs:sol_expr )) =>
      expandSolBinop BinOp.eqB lhs rhs
  | `(sol_expr| ( $lhs:sol_expr != $rhs:sol_expr )) =>
      expandSolBinop BinOp.neB lhs rhs
  | `(sol_expr| $c:sol_expr ? $t:sol_expr : $e:sol_expr) => do
      let cTerm ← expandSolExpr c
      let tTerm ← expandSolExpr t
      let eTerm ← expandSolExpr e
      `(SoliditySyntax.ternaryExpr $cTerm $tTerm $eTerm)
  | `(sol_expr| ! $arg:sol_expr) => do
      let argTerm ← expandSolExpr arg
      `(SoliditySyntax.unopExpr UnOp.not $argTerm)
  | `(sol_expr| - $arg:sol_expr) => do
      let argTerm ← expandSolExpr arg
      `(SoliditySyntax.unopExpr UnOp.neg $argTerm)
  | `(sol_expr| ++ $target:sol_expr) => do
      let targetTerm ← expandSolExpr target
      `(SoliditySyntax.incDecExpr IncDec.preInc $targetTerm)
  | `(sol_expr| $target:sol_expr ++) => do
      let targetTerm ← expandSolExpr target
      `(SoliditySyntax.incDecExpr IncDec.postInc $targetTerm)
  -- `predec(e)` / `postdec(e)` spell `--e` / `e--`; see the syntax
  -- declaration for why the Solidity operator cannot itself be a token.
  | `(sol_expr| predec($target:sol_expr)) => do
      let targetTerm ← expandSolExpr target
      `(SoliditySyntax.incDecExpr IncDec.preDec $targetTerm)
  | `(sol_expr| postdec($target:sol_expr)) => do
      let targetTerm ← expandSolExpr target
      `(SoliditySyntax.incDecExpr IncDec.postDec $targetTerm)
  -- `name@@Type[.field...]`: a state variable of a ported solkey contract.
  | `(sol_expr| $varName:ident @@ $path:ident) => do
      let parts := path.getId.components.map Lean.Name.toString
      match parts with
      | [tyName] =>
          `(SoliditySyntax.globalExpr $(quote varName.getId.toString)
              (SoliditySyntax.declTy $(quote tyName)))
      | tyName :: fields =>
          let mut acc ← `(SoliditySyntax.globalExpr
              $(quote varName.getId.toString)
              (SoliditySyntax.declTy $(quote tyName)))
          for field in fields do
            acc ← `(SoliditySyntax.fieldExpr $acc $(quote field))
          pure acc
      | [] => Macro.throwError "empty global path"
  -- Typed alias: sp@Account (simple), sp@Account.balance (field), sp@Account.token.value (nested).
  -- `pv@uint`/`rv@int`/`idx@uint` are stack values, not path aliases; see
  -- `isStackScratchAlias`.
  | `(sol_expr| $aliasName:ident @ $path:ident) => do
      let parts := path.getId.components.map Lean.Name.toString
      let name := aliasName.getId.toString
      match parts with
      | [tyName] =>
          if isStackScratchAlias name tyName then
            `(SoliditySyntax.varExpr Kind.stack
                (SoliditySyntax.declTy $(quote tyName)) $(quote name))
          else
            `(SoliditySyntax.aliasExpr $(quote name)
                (SoliditySyntax.declTy $(quote tyName)))
      | tyName :: fields =>
          let mut acc ← `(SoliditySyntax.aliasExpr $(quote name)
              (SoliditySyntax.declTy $(quote tyName)))
          for field in fields do
            acc ← `(SoliditySyntax.fieldExpr $acc $(quote field))
          pure acc
      | [] => Macro.throwError "empty alias path"
  | _ => Macro.throwUnsupported

partial def expandSolPlace : TSyntax `sol_expr -> MacroM (TSyntax `term)
  | `(sol_expr| ($inner:sol_expr)) => expandSolPlace inner
  | `(sol_expr| $name:ident) =>
      expandSolPathPlace (name.getId.components.map Lean.Name.toString)
  | `(sol_expr| $fnName:ident($args,*)) => do
      let parts := fnName.getId.components.map Lean.Name.toString
      match parts.reverse with
      | "push" :: targetRev =>
          if args.getElems.isEmpty && !targetRev.isEmpty then do
            let targetTerm ← expandSolPathPlace targetRev.reverse
            `(SoliditySyntax.pushPlace $targetTerm)
          else Macro.throwUnsupported
      | _ => Macro.throwUnsupported
  | `(sol_expr| $base:sol_expr . $field:ident) => do
      let baseTerm ← expandSolExpr base
      `(SoliditySyntax.fieldPlace $baseTerm $(quote field.getId.toString))
  | `(sol_expr| $base:sol_expr[$index:sol_expr]) => do
      let baseTerm ← expandSolExpr base
      let indexTerm ← expandSolExpr index
      `(SoliditySyntax.indexPlace $baseTerm $indexTerm)
  | `(sol_expr| $base:sol_expr .push()) => do
      let baseTerm ← expandSolPlace base
      `(SoliditySyntax.pushPlace $baseTerm)
  -- Typed alias place: sp@Account (simple), sp@Account.balance (field)
  | `(sol_expr| $varName:ident @@ $path:ident) => do
      let parts := path.getId.components.map Lean.Name.toString
      match parts with
      | [tyName] =>
          `(SoliditySyntax.globalPlace $(quote varName.getId.toString)
              (SoliditySyntax.declTy $(quote tyName)))
      | tyName :: fields =>
          let allButLast := fields.dropLast
          let lastField := fields.getLast!
          let mut acc ← `(SoliditySyntax.globalExpr
              $(quote varName.getId.toString)
              (SoliditySyntax.declTy $(quote tyName)))
          for field in allButLast do
            acc ← `(SoliditySyntax.fieldExpr $acc $(quote field))
          `(SoliditySyntax.fieldPlace $acc $(quote lastField))
      | [] => Macro.throwError "empty global path"
  | `(sol_expr| $aliasName:ident @ $path:ident) => do
      let parts := path.getId.components.map Lean.Name.toString
      let name := aliasName.getId.toString
      match parts with
      | [tyName] =>
          if isStackScratchAlias name tyName then
            `(SoliditySyntax.varPlace Kind.stack
                (SoliditySyntax.declTy $(quote tyName)) $(quote name))
          else
            `(SoliditySyntax.aliasPlace $(quote name)
                (SoliditySyntax.declTy $(quote tyName)))
      | tyName :: fields =>
          let allButLast := fields.dropLast
          let lastField := fields.getLast!
          let mut acc ← `(SoliditySyntax.aliasExpr $(quote name)
              (SoliditySyntax.declTy $(quote tyName)))
          for field in allButLast do
            acc ← `(SoliditySyntax.fieldExpr $acc $(quote field))
          `(SoliditySyntax.fieldPlace $acc $(quote lastField))
      | [] => Macro.throwError "empty alias path"
  | _ => Macro.throwUnsupported
end

partial def expandSolCallStmt (expr : TSyntax `sol_expr) : MacroM (Option (TSyntax `term)) := do
  match expr with
  | `(sol_expr| $fnName:ident($args,*)) =>
      let parts := fnName.getId.components.map Lean.Name.toString
      match parts.reverse with
      | "push" :: targetRev =>
          let targetParts := targetRev.reverse
          let targetTerm ← expandSolPathPlace targetParts
          match args.getElems.toList with
          | [] => pure (some (← `(Stmt.push $targetTerm none)))
          | [value] =>
              let valueTerm ← expandSolExpr value
              pure (some (← `(Stmt.push $targetTerm (some $valueTerm))))
          | _ => Macro.throwError "push expects zero or one argument"
      | "pop" :: targetRev =>
          if args.getElems.isEmpty then
            let targetTerm ← expandSolPathPlace targetRev.reverse
            pure (some (← `(Stmt.pop $targetTerm)))
          else
            Macro.throwError "pop expects no arguments"
      | "transfer" :: recipientRev =>
          match args.getElems.toList with
          | [amount] =>
              let recipientTerm ← expandSolPathExpr recipientRev.reverse
              let amountTerm ← expandSolExpr amount
              pure (some (← `(Stmt.transfer $recipientTerm $amountTerm)))
          | _ => Macro.throwError "transfer expects exactly one argument"
      | _ => pure none
  | _ => pure none

macro_rules
  | `(sexpr!{ $expr:sol_expr }) => expandSolExpr expr
  | `(splace!{ $place:sol_expr }) => expandSolPlace place
  | `(svar!{ $kindName:ident $tyName:ident $varName:ident }) =>
      `(SoliditySyntax.varPlace
          (SoliditySyntax.typedKind $(quote kindName.getId.toString))
          (SoliditySyntax.typedVarTy $(quote tyName.getId.toString))
          $(quote varName.getId.toString))
  | `(sfield!{ $kindName:ident $tyName:ident $pathName:ident }) => do
      let parts := pathName.getId.components.map Lean.Name.toString
      let fieldName ←
        match parts.getLast? with
        | some fieldName => pure fieldName
        | none => Macro.throwError "empty Solidity field path"
      let baseParts := parts.dropLast
      let baseTerm ← expandSolPathExpr baseParts
      `(PlaceExpr.field
          (SoliditySyntax.typedKind $(quote kindName.getId.toString))
          (SoliditySyntax.typedVarTy $(quote tyName.getId.toString))
          $baseTerm
          (SoliditySyntax.fieldFor
            $(quote fieldName)
            (SoliditySyntax.typedVarTy $(quote tyName.getId.toString))))

macro_rules
  | `(sstmt!{ $target:ident .push() = $rhs:sol_expr }) => do
      let targetTerm ← expandSolPathPlace (target.getId.components.map Lean.Name.toString)
      let rhsTerm ← expandSolExpr rhs
      `(Stmt.assign (SoliditySyntax.pushPlace $targetTerm) $rhsTerm)
  | `(sstmt!{ $target:ident .push() . $field:ident = $rhs:sol_expr }) => do
      let targetTerm ← expandSolPathPlace (target.getId.components.map Lean.Name.toString)
      let rhsTerm ← expandSolExpr rhs
      `(Stmt.assign
          (SoliditySyntax.fieldPlace
            (SoliditySyntax.pushPlaceExpr $targetTerm)
            $(quote field.getId.toString))
          $rhsTerm)
  | `(sstmt!{ $target:sol_expr .push() = $rhs:sol_expr }) => do
      let targetTerm ← expandSolPlace target
      let rhsTerm ← expandSolExpr rhs
      `(Stmt.assign (SoliditySyntax.pushPlace $targetTerm) $rhsTerm)
  | `(sstmt!{ $target:sol_expr .push() . $field:ident = $rhs:sol_expr }) => do
      let targetTerm ← expandSolPlace target
      let rhsTerm ← expandSolExpr rhs
      `(Stmt.assign
          (SoliditySyntax.fieldPlace
            (SoliditySyntax.pushPlaceExpr $targetTerm)
            $(quote field.getId.toString))
          $rhsTerm)
  | `(sstmt!{ $lhs:sol_expr = $rhs:sol_expr }) => do
      let lhsTerm ← expandSolPlace lhs
      let rhsTerm ← expandSolExpr rhs
      `(Stmt.assign $lhsTerm $rhsTerm)
  | `(sstmt!{ $firstName:ident $secondName:ident $varName:ident = $init:sol_expr }) => do
      let first := firstName.getId.toString
      let second := secondName.getId.toString
      let tyName := first
      let kindName := second
      match kindName with
      | "storage" => do
          let initTerm ← expandSolExpr init
          `(Stmt.storagePlaceAlias
              (SoliditySyntax.declTy $(quote tyName))
              $(quote varName.getId.toString)
              $initTerm)
      | "memory" => do
          let initTerm ← expandSolExpr init
          `(Stmt.memoryDecl
              (SoliditySyntax.declTy $(quote tyName))
              $(quote varName.getId.toString)
              (some $initTerm))
      | "stack" => do
          let initTerm ← expandSolExpr init
          `(Stmt.stackDecl
              (SoliditySyntax.declTy $(quote tyName))
              $(quote varName.getId.toString)
              (some $initTerm))
      | _ => Macro.throwError "expected storage, memory, or stack declaration"
  | `(sstmt!{ $firstName:ident $secondName:ident $varName:ident }) => do
      let first := firstName.getId.toString
      let second := secondName.getId.toString
      let tyName := first
      let kindName := second
      match kindName with
      | "storage" =>
          `(Stmt.storageDecl
              (SoliditySyntax.declTy $(quote tyName))
              $(quote varName.getId.toString)
              none)
      | "memory" =>
          `(Stmt.memoryDecl
              (SoliditySyntax.declTy $(quote tyName))
              $(quote varName.getId.toString)
              none)
      | "stack" =>
          `(Stmt.stackDecl
              (SoliditySyntax.declTy $(quote tyName))
              $(quote varName.getId.toString)
              none)
      | _ => Macro.throwError "expected storage, memory, or stack declaration"
  | `(sstmt!{ $tyName:ident $varName:ident = $init:sol_expr }) => do
      let initTerm ← expandSolExpr init
      `(Stmt.stackDecl
          (SoliditySyntax.declTy $(quote tyName.getId.toString))
          $(quote varName.getId.toString)
          (some $initTerm))
  | `(sstmt!{ $tyName:ident $varName:ident }) =>
      `(Stmt.stackDecl
          (SoliditySyntax.declTy $(quote tyName.getId.toString))
          $(quote varName.getId.toString)
          none)
  | `(sstmt!{ delete $target:sol_expr }) => do
      let targetTerm ← expandSolPlace target
      `(Stmt.delete $targetTerm)
  | `(sstmt!{ $target:sol_expr .push($value:sol_expr) }) => do
      let targetTerm ← expandSolPlace target
      let valueTerm ← expandSolExpr value
      `(Stmt.push $targetTerm (some $valueTerm))
  | `(sstmt!{ $target:sol_expr .push() }) => do
      let targetTerm ← expandSolPlace target
      `(Stmt.push $targetTerm none)
  | `(sstmt!{ $target:sol_expr .pop() }) => do
      let targetTerm ← expandSolPlace target
      `(Stmt.pop $targetTerm)
  | `(sstmt!{ $expr:sol_expr }) => do
      match (← expandSolCallStmt expr) with
      | some stmtTerm => pure stmtTerm
      | none =>
          let exprTerm ← expandSolExpr expr
          `(Stmt.expr $exprTerm)

macro_rules
  | `(sstmt!{ $lhs:sol_expr += $rhs:sol_expr }) => do
      let lhsTerm ← expandSolPlace lhs
      let rhsTerm ← expandSolExpr rhs
      `(Stmt.compoundAssign BinOp.add $lhsTerm $rhsTerm)
  | `(sstmt!{ $lhs:sol_expr -= $rhs:sol_expr }) => do
      let lhsTerm ← expandSolPlace lhs
      let rhsTerm ← expandSolExpr rhs
      `(Stmt.compoundAssign BinOp.sub $lhsTerm $rhsTerm)
  | `(sstmt!{ $lhs:sol_expr *= $rhs:sol_expr }) => do
      let lhsTerm ← expandSolPlace lhs
      let rhsTerm ← expandSolExpr rhs
      `(Stmt.compoundAssign BinOp.mul $lhsTerm $rhsTerm)
  | `(sstmt!{ $lhs:sol_expr /= $rhs:sol_expr }) => do
      let lhsTerm ← expandSolPlace lhs
      let rhsTerm ← expandSolExpr rhs
      `(Stmt.compoundAssign BinOp.div $lhsTerm $rhsTerm)
  | `(sstmt!{ $lhs:sol_expr %= $rhs:sol_expr }) => do
      let lhsTerm ← expandSolPlace lhs
      let rhsTerm ← expandSolExpr rhs
      `(Stmt.compoundAssign BinOp.mod $lhsTerm $rhsTerm)
  | `(sstmt!{ assert($cond:sol_expr) }) => do
      let condTerm ← expandSolExpr cond
      `(Stmt.assertStmt $condTerm)
  | `(sstmt!{ require($cond:sol_expr) }) => do
      let condTerm ← expandSolExpr cond
      `(Stmt.requireStmt $condTerm)
  | `(sstmt!{ revert() }) =>
      `(Stmt.revert none)
  | `(sstmt!{ if ($cond:sol_expr) { $thn;* } else { $els;* } }) => do
      let condTerm ← expandSolExpr cond
      let thnTerms ← thn.getElems.mapM fun s => `(sstmt!{ $s })
      let elsTerms ← els.getElems.mapM fun s => `(sstmt!{ $s })
      `(Stmt.ite $condTerm [ $thnTerms,* ] [ $elsTerms,* ])
  | `(sstmt!{ if ($cond:sol_expr) { $thn;* } }) => do
      let condTerm ← expandSolExpr cond
      let thnTerms ← thn.getElems.mapM fun s => `(sstmt!{ $s })
      `(Stmt.ite $condTerm [ $thnTerms,* ] [])
  | `(sstmt!{ $recipient:sol_expr .transfer($amount:sol_expr) }) => do
      let recipientTerm ← expandSolExpr recipient
      let amountTerm ← expandSolExpr amount
      `(Stmt.transfer $recipientTerm $amountTerm)

/-- Build the `Block` term of a `sol_stmt` sequence, honouring a trailing
`.. name` context splice (see the `sol_stmt` production): the listed
statements are appended in front of `name`.  A splice anywhere but last is an
error -- it would not denote a block. -/
def expandSolBlock (stmts : Array (TSyntax `sol_stmt)) :
    MacroM (TSyntax `term) := do
  let isSplice (s : TSyntax `sol_stmt) : Bool :=
    match s with | `(sol_stmt| .. $_:ident) => true | _ => false
  match stmts.back? with
  | some tail@(_) =>
      if isSplice tail then
        let front := stmts.pop
        if front.any isSplice then
          Macro.throwErrorAt tail
            "a `.. name` context splice may only be the last statement"
        let stmtTerms ← front.mapM fun s => `(sstmt!{ $s })
        match tail with
        | `(sol_stmt| .. $name:ident) => `([ $stmtTerms,* ] ++ $name)
        | _ => Macro.throwUnsupported
      else
        if stmts.any isSplice then
          Macro.throwErrorAt tail
            "a `.. name` context splice may only be the last statement"
        let stmtTerms ← stmts.mapM fun s => `(sstmt!{ $s })
        `([ $stmtTerms,* ])
  | none => `(([] : Block))

syntax "sblock!" "{" sepBy(sol_stmt, ";", ";") "}" : term

macro_rules
  | `(sblock!{ $stmts;* }) => expandSolBlock stmts.getElems

namespace TypedStmt

inductive StorageDecl where
  | alias {ref : RefTy} (name : Name) (init : Place Kind.storage (Ty.ref ref))

inductive MemoryDecl where
  | fresh (name : Name) (ref : RefTy) (ok : ref.allowsMemory = true)
  | alias {ref : RefTy} (name : Name) (init : Place Kind.memory (Ty.ref ref))
  | copy {ref : RefTy} (name : Name) (init : Place Kind.storage (Ty.ref ref))

inductive StackDecl where
  | init {ty : Ty} (name : Name) (primitive : ty.isPrimitive = true)
      (value : Expr Kind.stack ty)

inductive Assign where
  /-- `target = value`.  A storage-to-storage copy of a type that carries a
  mapping is not a statement: solc ≥ 0.7 rejects it and so does solkey's
  parser (`ParserUtils.parseAssignmentMaybe`), so `mapFree` is the obligation
  that makes it unconstructible here.  Discharged by evaluation on closed
  types; the kind-mismatch cases close by `simp` on the kinds. -/
  | mk {targetKind valueKind ty : _}
      (target : Place targetKind ty) (value : Expr valueKind ty)
      (mapFree : targetKind = Kind.storage -> valueKind = Kind.storage ->
          Semantics.tyHasMapping ty = false := by
        simp [Semantics.tyHasMapping, Semantics.fieldsHaveMapping, Semantics.structDef])
  | storageFromMemory {ref : RefTy}
      (target : Place Kind.storage (Ty.ref ref))
      (value : Expr Kind.memory (Ty.ref ref))

inductive Stmt where
  | expr {kind ty : _} (expr : Expr kind ty)
  | assign (assign : Assign)
  | storageDecl (decl : StorageDecl)
  | memoryDecl (decl : MemoryDecl)
  | stackDecl (decl : StackDecl)
  | delete {kind ty : _} (target : Place kind ty)
  | push {elem : Ty}
      (target : Place Kind.storage (Ty.ref (RefTy.array elem)))
      (value : Option (Expr Kind.stack elem))
  | pop {elem : Ty} (target : Place Kind.storage (Ty.ref (RefTy.array elem)))

namespace Assign

end Assign

namespace StorageDecl

end StorageDecl

namespace MemoryDecl

end MemoryDecl

namespace StackDecl

end StackDecl

end TypedStmt

namespace Examples

def personTy : Ty :=
  Ty.ref (RefTy.struct "Person")

def accountTy : Ty :=
  Ty.ref (RefTy.struct "Account")

def tokenTy : Ty :=
  Ty.ref (RefTy.struct "Token")

def personRef : RefTy := RefTy.struct "Person"
def accountRef : RefTy := RefTy.struct "Account"
def tokenRef : RefTy := RefTy.struct "Token"

def alice : Place Kind.storage personTy :=
  Typed.Place.storageVar "alice" personRef

def accountF : Typed.RefField personRef accountRef :=
  { name := "account", refSort := rfl }

def tokenF : Typed.RefField accountRef tokenRef :=
  { name := "token", refSort := rfl }

def valueF : Typed.PrimField tokenRef PrimTy.uint :=
  { name := "value" }

def account : Place Kind.storage accountTy :=
  Typed.Place.fieldRef alice accountF

def token : Place Kind.storage tokenTy :=
  Typed.Place.fieldRef account tokenF

def tokenValue : Place Kind.storage Ty.uint :=
  Typed.Place.fieldPrim token valueF

def carol : Place Kind.memory personTy :=
  Typed.Place.memoryVar "carol" personRef rfl

def amount : Place Kind.stack Ty.uint :=
  Typed.Place.stackVar "amount" Ty.uint rfl

def storageFieldAssignment : TypedStmt.Stmt :=
  TypedStmt.Stmt.assign
    (TypedStmt.Assign.mk tokenValue (Typed.Expr.place amount))

def storageAlias : TypedStmt.StorageDecl :=
  TypedStmt.StorageDecl.alias "v" account

/- The invalid Solidity line `Account storage v = carol` is unconstructible:
   `carol` has type `Place Kind.memory personTy`, while storage aliases require
   `Place Kind.storage personTy`. -/

/- The invalid Solidity line `ledger2 = ledger` is unconstructible as well:
   `Ledger` carries `balances : mapping(uint => uint)`, so `Assign.mk`'s
   `mapFree` obligation for a storage-to-storage copy at that type is false —
   the auto-param fails exactly where solc ≥ 0.7 and solkey's parser do. -/
example :
    ¬ (Kind.storage = Kind.storage -> Kind.storage = Kind.storage ->
        Semantics.tyHasMapping (Ty.ref (RefTy.struct "Ledger")) = false) := by
  simp [Semantics.tyHasMapping, Semantics.fieldsHaveMapping, Semantics.structDef]

#check storageFieldAssignment
#check storageAlias

#check sexpr!{ alice.account.token.value }
#check splace!{ alice.account.token.value }
#check sexpr!{ people[i] }
#check sexpr!{ nextIndex(flag, true) }
#check sexpr!{ flag && true }
#check sstmt!{ alice.account.token.value = amount }
#check sstmt!{ Person storage alice = bob }
#check sstmt!{ Person memory carol = alice }
#check sstmt!{ bool flag = true }
#check sstmt!{ delete alice.account }
#check sstmt!{ people.push(bob) }
#check Stmt.assign
  (SoliditySyntax.pushPlace (SoliditySyntax.rootPlace "people"))
  (SoliditySyntax.rootExpr "bob")
#check Stmt.assign
  (SoliditySyntax.fieldPlace
    (SoliditySyntax.pushPlaceExpr (SoliditySyntax.rootPlace "people")) "age")
  (SoliditySyntax.rootExpr "amount")
#check sstmt!{ people.push() }
#check sstmt!{ people.pop() }
#check svar!{ storage Person sp }
#check sfield!{ storage uint alice.value }

-- Test new typed alias syntax
#check sexpr!{ sp@Account }
#check splace!{ sp@Account }
#check sexpr!{ sp@Account.balance }
#check splace!{ sp@Account.balance }
#check sexpr!{ mv@Person }
#check splace!{ mv@Person }
#check sstmt!{ Account storage sp = alice.account }
#check sstmt!{ sp@Account.balance = amount }
-- Test alias index access
def personArrayTy : Ty := Ty.ref (RefTy.array personTy)
#check sexpr!{ sp@Person[i] }
#check splace!{ sp@Person[i] }

#check_failure Stmt.delete (WrappedExpr.call Kind.storage Ty.uint "f" [])

end Examples

inductive SolidityModality where
  | box
  | diamond
  | both
  deriving DecidableEq, Repr

/-! ## Function table and inlining (KeY `functionBodyExpand`)

KeY's `functionBodyExpand` taclet delegates to the `ExpandFunctionBody`
metaconstruct: fresh parameter declarations initialized with the
actuals, a fresh uninitialized declaration for the single *named
return*, the (renamed) body, and the assignment of the return variable
to the call's result place. KeY obtains freshness by object identity;
here the fixed test-contract table stores bodies already alpha-renamed
to `fn$`-prefixed names, which by convention no caller program uses
(the same discipline as the `pv`/`sp` capture aliases). Constraints
mirrored from solkey: one named return, no overloading (the table is
name-keyed), no recursion (see `blockCallFree` lock-ins in
`Examples/Taclets/FunctionCallOps.lean`). -/

structure FunDecl where
  params : List (Ty × Name)
  ret : Option (Ty × Name)
  body : Block

namespace SoliditySyntax

/-- The test-contract function table (the `structDef` analogue for
functions). -/
def funDef : Name -> Option FunDecl
  | "addOne" => some {
      params := [(Ty.uint, "addOne$x")]
      ret := some (Ty.uint, "addOne$r")
      body := [ Stmt.assign (varPlace Kind.stack Ty.uint "addOne$r")
          (WrappedExpr.binop BinOp.add
            (varExpr Kind.stack Ty.uint "addOne$x")
            (intLitExpr 1)) ] }
  | "double" => some {
      params := [(Ty.uint, "double$x")]
      ret := some (Ty.uint, "double$r")
      body := [ Stmt.assign (varPlace Kind.stack Ty.uint "double$r")
          (WrappedExpr.binop BinOp.add
            (varExpr Kind.stack Ty.uint "double$x")
            (varExpr Kind.stack Ty.uint "double$x")) ] }
  | "inc2" => some {
      params := [(Ty.uint, "inc2$x")]
      ret := some (Ty.uint, "inc2$r")
      body := [ Stmt.callStmt
            (some (varPlace Kind.stack Ty.uint "inc2$r")) "addOne"
            [varExpr Kind.stack Ty.uint "inc2$x"],
          Stmt.callStmt
            (some (varPlace Kind.stack Ty.uint "inc2$r")) "addOne"
            [varExpr Kind.stack Ty.uint "inc2$r"] ] }
  | _ => none

def paramDecls (params : List (Ty × Name)) (args : List WrappedExpr) :
    Block :=
  (params.zip args).map fun pa => Stmt.stackDecl pa.1.1 pa.1.2 (some pa.2)

def retDecl : Option (Ty × Name) -> Block
  | some (ty, r) => [Stmt.stackDecl ty r none]
  | none => []

/-- One expansion of `result = fn(args);` per KeY `ExpandFunctionBody`.
`none` where solkey's converter would have rejected the call: unknown
function, arity mismatch, or a result place without a named return. -/
def expandCall (res : Option PlaceExpr) (fn : Name)
    (args : List WrappedExpr) : Option Block :=
  match funDef fn with
  | none => none
  | some d =>
      if args.length = d.params.length then
        match res, d.ret with
        | some lhs, some (ty, r) =>
            some (paramDecls d.params args ++ retDecl d.ret ++ d.body ++
              [Stmt.assign lhs (varExpr Kind.stack ty r)])
        | none, _ =>
            some (paramDecls d.params args ++ retDecl d.ret ++ d.body)
        | some _, none => none
      else none

mutual
/-- Fuel-bounded call inlining. Out of fuel (or an unexpandable call)
leaves the `callStmt` in place, where the interpreter is stuck — the
analogue of an unprovable KeY goal. -/
def inlineStmt : Nat -> Stmt -> Block
  | fuel, Stmt.ite c thn els =>
      [Stmt.ite c (inlineBlock fuel thn) (inlineBlock fuel els)]
  | fuel + 1, Stmt.callStmt res fn args =>
      match expandCall res fn args with
      | some blk => inlineBlock fuel blk
      | none => [Stmt.callStmt res fn args]
  | 0, Stmt.callStmt res fn args => [Stmt.callStmt res fn args]
  | _, stmt => [stmt]

def inlineBlock : Nat -> Block -> Block
  | _, [] => []
  | fuel, stmt :: rest => inlineStmt fuel stmt ++ inlineBlock fuel rest
end

theorem inlineBlock_nil (fuel : Nat) : inlineBlock fuel [] = [] := by
  rw [inlineBlock]

theorem inlineBlock_cons (fuel : Nat) (stmt : Stmt) (rest : Block) :
    inlineBlock fuel (stmt :: rest) =
      inlineStmt fuel stmt ++ inlineBlock fuel rest := by
  rw [inlineBlock]

/-- The rewrite-layer soundness anchor for `functionBodyExpand`: one
inlining step of a call is the inlining of its expansion — the rule's
residual and the interpreter's (inlined) reading of the call coincide
definitionally. -/
theorem inlineStmt_callStmt (fuel : Nat) (res : Option PlaceExpr)
    (fn : Name) (args : List WrappedExpr) (blk : Block)
    (h : expandCall res fn args = some blk) :
    inlineStmt (fuel + 1) (Stmt.callStmt res fn args) =
      inlineBlock fuel blk := by
  rw [inlineStmt, h]

mutual
/-- No `callStmt` anywhere in the statement. -/
def stmtCallFree : Stmt -> Bool
  | Stmt.ite _ thn els => blockCallFree thn && blockCallFree els
  | Stmt.callStmt _ _ _ => false
  | _ => true

def blockCallFree : Block -> Bool
  | [] => true
  | stmt :: rest => stmtCallFree stmt && blockCallFree rest
end

mutual
/-- Inlining is the identity on call-free statements. -/
theorem inlineStmt_id_of_callFree (fuel : Nat) :
    ∀ stmt, stmtCallFree stmt = true -> inlineStmt fuel stmt = [stmt]
  | Stmt.ite c thn els, h => by
      simp only [stmtCallFree, Bool.and_eq_true] at h
      rw [inlineStmt, inlineBlock_id_of_callFree fuel thn h.1,
        inlineBlock_id_of_callFree fuel els h.2]
  | Stmt.callStmt _ _ _, h => by simp [stmtCallFree] at h
  | Stmt.expr _, _ => by cases fuel <;> simp [inlineStmt]
  | Stmt.assign _ _, _ => by cases fuel <;> simp [inlineStmt]
  | Stmt.storageDecl _ _ _, _ => by cases fuel <;> simp [inlineStmt]
  | Stmt.storagePlaceAlias _ _ _, _ => by cases fuel <;> simp [inlineStmt]
  | Stmt.memoryDecl _ _ _, _ => by cases fuel <;> simp [inlineStmt]
  | Stmt.stackDecl _ _ _, _ => by cases fuel <;> simp [inlineStmt]
  | Stmt.delete _, _ => by cases fuel <;> simp [inlineStmt]
  | Stmt.push _ _, _ => by cases fuel <;> simp [inlineStmt]
  | Stmt.pushAssign _ _, _ => by cases fuel <;> simp [inlineStmt]
  | Stmt.pushFieldAssign _ _ _, _ => by cases fuel <;> simp [inlineStmt]
  | Stmt.pop _, _ => by cases fuel <;> simp [inlineStmt]
  | Stmt.revert _, _ => by cases fuel <;> simp [inlineStmt]
  | Stmt.compoundAssign _ _ _, _ => by cases fuel <;> simp [inlineStmt]
  | Stmt.assertStmt _, _ => by cases fuel <;> simp [inlineStmt]
  | Stmt.requireStmt _, _ => by cases fuel <;> simp [inlineStmt]
  | Stmt.transfer _ _, _ => by cases fuel <;> simp [inlineStmt]

/-- Inlining is the identity on call-free blocks. -/
theorem inlineBlock_id_of_callFree (fuel : Nat) :
    ∀ blk, blockCallFree blk = true -> inlineBlock fuel blk = blk
  | [], _ => by rw [inlineBlock]
  | stmt :: rest, h => by
      simp only [blockCallFree, Bool.and_eq_true] at h
      rw [inlineBlock, inlineStmt_id_of_callFree fuel stmt h.1,
        inlineBlock_id_of_callFree fuel rest h.2]
      rfl
end

end SoliditySyntax

structure SolidityBlock where
  modality : SolidityModality
  stmts : Block
  deriving Repr

syntax "solbox!" "{" sepBy(sol_stmt, ";", ";") "}" : term
syntax "soldiamond!" "{" sepBy(sol_stmt, ";", ";") "}" : term
syntax "solboth!" "{" sepBy(sol_stmt, ";", ";") "}" : term

macro_rules
  | `(solbox!{ $stmts;* }) => do
      `(SolidityBlock.mk .box $(← expandSolBlock stmts.getElems))
  | `(soldiamond!{ $stmts;* }) => do
      `(SolidityBlock.mk .diamond $(← expandSolBlock stmts.getElems))
  | `(solboth!{ $stmts;* }) => do
      `(SolidityBlock.mk .both $(← expandSolBlock stmts.getElems))

/-- A dynamic-logic judgment `[b] post` / `<b> post`: run the block under the
given modality and evaluate the postcondition (a Boolean expression) in the
final state. Semantics in `Semantics.lean`. -/
structure SolidityJudgment where
  block : SolidityBlock
  post : WrappedExpr
  deriving Repr

/-! ### The postcondition position

A judgment's postcondition is a `WrappedExpr`, and the calculus writes it as the
opaque symbol `φ` on every line of every chain: the rules never look at it, so
spelling out a concrete Boolean is noise that obscures exactly that.  A
`sol_post` is therefore *either* a concrete `sol_expr` (what the
`native_decide` examples need, since they evaluate it) *or* `‹t›`, an escape to
an arbitrary Lean term of type `WrappedExpr` -- so a derivation over
`variable (φ : WrappedExpr)` reads as the calculus's `⟨[…]⟩φ`.

Deliberately a category of its own, used *only* in the post position, rather
than a general `sol_expr` splice: an escape hatch available everywhere becomes
the house style, and the point of `sol_expr` is that programs are written as
programs. -/
declare_syntax_cat sol_post
/-- A concrete postcondition, in the ordinary Solidity expression grammar. -/
syntax sol_expr : sol_post
/-- An opaque postcondition: any Lean term of type `WrappedExpr`, typically a
`variable (φ : WrappedExpr)`. This is the calculus's `φ`. -/
syntax "‹" term "›" : sol_post

def expandSolPost : TSyntax `sol_post → MacroM (TSyntax `term)
  | `(sol_post| ‹$t:term›) => pure t
  | `(sol_post| $e:sol_expr) => expandSolExpr e
  | stx => Macro.throwErrorAt stx "unexpected Solidity postcondition"

/-- `sol!{ < stmts > (post) }` (diamond), `sol!{ [ stmts ] (post) }` (box) and
`sol!{ <[ stmts ]> (post) }` (the combined modality).  The postcondition is a
parenthesized expression or the opaque `‹φ›`, e.g.
`sol!{ < alice.account.balance = 10; result = alice.account.balance >
(result == 10) }` and `sol!{ <[ alice.account.balance = 10 ]> ‹φ› }`.

`<[ … ]>` is the calculus's `\dlbothfphi` (`macros.sty:118`), which is the
*default* modality of every worked example: a rule stated under it holds for
box and diamond alike.  ASCII `<[`/`]>` rather than the calculus's
`⟨\![ … ]\!⟩`, because `⟨[` would re-tokenise every anonymous constructor
whose first component is a list. -/
syntax "sol!" "{" "<" sepBy(sol_stmt, ";", ";") ">" sol_post "}" : term
syntax "sol!" "{" "[" sepBy(sol_stmt, ";", ";") "]" sol_post "}" : term
syntax "sol!" "{" "<[" sepBy(sol_stmt, ";", ";") "]>" sol_post "}" : term

macro_rules
  | `(sol!{ < $stmts;* > $post:sol_post }) => do
      let blockTerm ← expandSolBlock stmts.getElems
      let postTerm ← expandSolPost post
      `(SolidityJudgment.mk (SolidityBlock.mk .diamond $blockTerm) $postTerm)
  | `(sol!{ [ $stmts;* ] $post:sol_post }) => do
      let blockTerm ← expandSolBlock stmts.getElems
      let postTerm ← expandSolPost post
      `(SolidityJudgment.mk (SolidityBlock.mk .box $blockTerm) $postTerm)
  | `(sol!{ <[ $stmts;* ]> $post:sol_post }) => do
      let blockTerm ← expandSolBlock stmts.getElems
      let postTerm ← expandSolPost post
      `(SolidityJudgment.mk (SolidityBlock.mk .both $blockTerm) $postTerm)

namespace SolidityBlockExamples

#check solbox!{ alice.account.balance = amount; delete alice.account }
#check soldiamond!{ Person storage p = bob }
#check solboth!{ alice.account.balance = amount }
#check sexpr!{ i + 1 }
#check sexpr!{ (amount < 10) && flag }
#check sexpr!{ 2 ** 8 - 1 }
#check sexpr!{ !flag || (i == amount) }
#check sexpr!{ ++i }
#check sexpr!{ i++ }
#check sstmt!{ alice.age += 2 }
#check sstmt!{ assert(flag) }
#check sstmt!{ revert() }
#check sstmt!{ if (flag) { i = 1 } else { i = 2 } }
#check sstmt!{ bob.transfer(amount) }
#check sol!{ < alice.account.balance = 10;
              result = alice.account.balance > (result == 10) }
#check sol!{ [ i = i + 1 ] (i > 0) }
-- The calculus's default modality and its opaque postcondition
-- (`macros.sty:118`, `\dlbothfphi`).
#check sol!{ <[ alice.account.balance = 10 ]> (alice.account.balance == 10) }
section
variable (φ : WrappedExpr)
#check sol!{ <[ alice.account.balance = 10 ]> ‹φ› }
#check sol!{ [ alice.account.balance = 10 ] ‹φ› }
#check sol!{ < alice.account.balance = 10 > ‹φ› }
#check sol!{ <[ ]> ‹φ› }
end

/-! The scratch value aliases the capture rules bind on the stack
(`isStackScratchAlias`).  `pv@uint` has to work as a binop operand, as an
assignment target, inside `assert(...)`/`transfer(...)` and as a branch
condition -- those are the shapes that used to force raw `Stmt` constructors in
`Examples/Derivations/ValueCapture.lean`. -/
#check sexpr!{ pv@uint + amount }
#check sexpr!{ pv@bool }
#check splace!{ pv@uint }
#check sstmt!{ pv@uint = x + y }
#check sstmt!{ result = pv@uint + amount }
#check sstmt!{ assert(pv@bool) }
#check sstmt!{ to.transfer(pv@uint) }
#check sstmt!{ if (pv@bool) { total = 1 } else { total = 2 } }
#check sstmt!{ uint rv = 34 }
#check sstmt!{ alice.age = rv@uint }
#check sexpr!{ values[idx@uint] }
-- A *reference*-typed alias keeps its path-alias kind (memory here).
#check sexpr!{ pv@Account.balance }

/-! A trailing `.. name` context splice names the inactive suffix (the
calculus's `omega`) instead of retyping it on every line of a derivation. -/
section
variable (rest : Block)
#check solbox!{ alice.age = 34; .. rest }
#check solbox!{ .. rest }
#check sblock!{ result = alice.age; .. rest }
#check sol!{ < alice.age = 34; .. rest > (alice.age == 34) }
end

end SolidityBlockExamples

end Solidity
