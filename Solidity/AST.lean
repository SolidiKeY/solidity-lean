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

The syntax as written is `Syntax.lean`, scoped in `Syntax/Scoped.lean`
(contexts in `Scope.lean`); the run is `Semantics/Run.lean` over
`State C Γ`, and `Semantics.lean` holds the state's untyped operations.
-/

namespace Solidity

abbrev Name := String


/-- KeY `int, bool \extends Prim` (`intHeader.key`, `boolHeader.key`).
KeY has a single mathematical `int` sort; the calculus keeps solc's
`uint`/`int` distinction below `Prim` — both erase to KeY `int`
(range checking is `PrimTy.ofInt?`'s job, not the sort's). -/
inductive PrimTy where
  | bool
  | uint
  | int
  deriving DecidableEq, Repr

namespace PrimTy

/-- The Solidity spelling. -/
def toStr : PrimTy → String
  | .uint => "uint" | .int => "int" | .bool => "bool"

/-- A primitive type by its Solidity name: the one table of them.  An
`address` (and an `address payable`) is a `uint`; `uint256` and `int256` are
`uint` and `int`.  The narrower widths are not types: a `uint8` local is a
`uint` whose width the elaborator carries (`narrowTy?`, `Syntax.lean`). -/
def ofName? : String → Option PrimTy
  | "uint" | "uint256" | "address" => some .uint
  | "int" | "int256" => some .int
  | "bool" => some .bool
  | _ => none

end PrimTy

/-- Why the type name `s` is refused: neither a primitive type, nor a struct
of `Semantics.structDef`, nor an enum of the contract. -/
def unknownTyMsg (s : String) : String :=
  let hint :=
    if s.startsWith "uint" || s.startsWith "int" then
      ": the integer types are `uint8` … `uint256` and `int8` … `int256`, in steps of 8"
    else if s.startsWith "bytes" || s == "string" || s == "byte" then
      ": `bytes` and `string` are not modelled"
    else ""
  s!"unknown type {s}{hint}"

mutual
  inductive RefTy where
    | struct (name : Name)
    | array (elem : Ty)
    /-- `T[n]`: a fixed-size array, its length part of the type. -/
    | fixed (elem : Ty) (n : Nat)
    /-- `mapping(K => V)`: a key is a value type (solc rejects any other). -/
    | mapping (key : PrimTy) (value : Ty)
    deriving DecidableEq, Repr

  /-- KeY `Prim, Struct \extends StValue` (`solidityDLHeader.key`,
  `structHeader.key`): a type is a primitive sort or a reference sort. -/
  inductive Ty where
    | prim (p : PrimTy)
    | ref (ref : RefTy)
    deriving DecidableEq, Repr
end

instance : Coe PrimTy Ty := ⟨Ty.prim⟩

/-- Outer-array copy compatibility: fixed `n` into a dynamic array, or into
a fixed array with room for every source element. The element type stays
intrinsic; the dynamic length bound and the absence of truncation are evidence. -/
inductive FixedCopy (E : Ty) (n : Nat) : RefTy → Type where
  | dynamic (bound : n < 2 ^ 256) : FixedCopy E n (.array E)
  | fixed (m : Nat) (fits : n ≤ m) : FixedCopy E n (.fixed E m)

/-- Reify a fixed-to-dynamic witness using a kernel-rechecked Boolean fact. -/
def FixedCopy.dynamicChecked (E : Ty) (n : Nat) (h : decide (n < 2 ^ 256) = true) :
    FixedCopy E n (.array E) := .dynamic (of_decide_eq_true h)

/-- Reify a fixed-to-fixed witness without trusting an elaborator proof. -/
def FixedCopy.fixedChecked (E : Ty) (n m : Nat) (h : decide (n ≤ m) = true) :
    FixedCopy E n (.fixed E m) := .fixed m (of_decide_eq_true h)

/-- Resolve a fixed-array source at a compatible destination shape. -/
def FixedCopy.ofTarget (E : Ty) (n : Nat) : (R : RefTy) → Option (FixedCopy E n R)
  | .array E' =>
    if he : E = E' then
      if hb : n < 2 ^ 256 then some (he ▸ FixedCopy.dynamic hb) else none
    else none
  | .fixed E' m =>
    if he : E = E' then
      if hf : n ≤ m then some (he ▸ FixedCopy.fixed m hf) else none
    else none
  | _ => none

/-- At fixed source and destination types, shape compatibility has one
witness; its bound evidence is proof-irrelevant. -/
theorem FixedCopy.eq {E : Ty} {n : Nat} {R : RefTy} (a b : FixedCopy E n R) : a = b := by
  cases a <;> cases b <;> rfl

namespace Ty

/- Source-level names of the primitive types, usable in patterns. -/
@[match_pattern] abbrev bool : Ty := .prim .bool
@[match_pattern] abbrev uint : Ty := .prim .uint
@[match_pattern] abbrev int : Ty := .prim .int

def isPrimitive : Ty -> Bool
  | prim _ => true
  | ref _ => false

def isReference (ty : Ty) : Bool :=
  !ty.isPrimitive

/-- A mapping: `mapping(uint => uint)`, the element of `mapping(uint => uint)[]`
that `pop` leaves as it is (solkey's `mappingElement`). -/
def isMapping : Ty -> Bool
  | ref (.mapping ..) => true
  | _ => false

/-- The element type of an array, dynamic or fixed, is a mapping
(`Path[…,mappingElement]`): `false` for anything that is not an array. -/
def elemIsMapping : Ty -> Bool
  | ref (.array e) => e.isMapping
  | ref (.fixed e _) => e.isMapping
  | _ => false

/-- The element type of an array is primitive (`Path[…,primitiveElement]`):
`false` for anything that is not an array. -/
def elemIsPrim : Ty -> Bool
  | ref (.array e) => e.isPrimitive
  | ref (.fixed e _) => e.isPrimitive
  | _ => false

end Ty

def PrimTy.isNumeric : PrimTy -> Bool
  | .uint | .int => true
  | .bool => false

/-- `n` is a value of the numeric type `p`: a `uint` is below `2^256`, an
`int` in `[-2^255, 2^255)`; no number is a `bool`.  What a literal's type
proves of it (`Simple.lit`), so a literal out of its type's range is not a
program, as solc rejects it. -/
def PrimTy.inRange : PrimTy → Int → Bool
  | .uint, n => decide (0 ≤ n ∧ n < ((2 ^ 256 : Nat) : Int))
  | .int, n => decide (-((2 ^ 255 : Nat) : Int) ≤ n ∧ n < ((2 ^ 255 : Nat) : Int))
  | .bool, _ => false

mutual
  def Ty.allowsMemory : Ty -> Bool
    | Ty.ref ref => ref.allowsMemory
    | Ty.prim _ => true

  def RefTy.allowsMemory : RefTy -> Bool
    | RefTy.struct _ => true
    | RefTy.array elem => elem.allowsMemory
    | RefTy.fixed elem _ => elem.allowsMemory
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
  | Ty.ref (RefTy.fixed _ _) => true
  | _ => false

/-! ### The struct schema and `containsMapping`

The struct table and the type predicate that reads it live here rather than
in `Semantics.lean` because they are facts about *static types*, and the
typed AST needs one of them: `Src.copy` refuses a storage-to-storage
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
unknown struct name has zero fields, so `SVal.dflt` builds an empty
node for it instead of being `undef`.  Harmless while the contract corpus
is closed; making it loud would mean an `Option` result threaded through
`SVal.dflt`, `tyHasMapping` and the reachability proofs. -/
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
       ("stash", Ty.ref (RefTy.mapping .uint Ty.uint))]
  -- TestSuite.sol (`keyext.solidity.examples/TestSuite.sol`); `Basket`
  -- is shared verbatim with `solc/SolcMemory.sol`.
  | "Basket" => [("items", Ty.ref (RefTy.array Ty.uint))]
  | "Ledger" =>
      [("nonce", Ty.uint),
       ("balances", Ty.ref (RefTy.mapping .uint Ty.uint))]
  | "LedgerUse" => [("ledger", Ty.ref (RefTy.struct "Ledger"))]
  | "TokenBucket" =>
      [("tokens", Ty.ref (RefTy.array (Ty.ref (RefTy.struct "Token"))))]
  | "Toggle" => [("on", Ty.bool), ("n", Ty.uint)]
  -- TestSuite.sol's `Triple { uint[3] items; uint tag; }`, renamed: `Triple`
  -- is `SolcStructs.sol`'s three `uint`s.
  | "FixedTriple" => [("items", Ty.ref (RefTy.fixed Ty.uint 3)), ("tag", Ty.uint)]
  -- solc/SolcArrays.sol, SolcControlFlow.sol, SolcStructs.sol (agree).
  | "Pair" => [("a", Ty.uint), ("b", Ty.uint)]
  | "FileLevelPair" => [("left", Ty.uint), ("right", Ty.uint)]
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
  -- solc/open/SolcConstructorsOpen.sol, SolcLoopsOpen.sol.
  | "D" => [("p", Ty.uint), ("q", Ty.bool)]
  | "Nest" => [("d", Ty.ref (RefTy.array (Ty.ref (RefTy.array Ty.uint))))]
  -- solc/open/NarrowNested.sol: narrow members (`structWidths`).
  | "Packed" =>
      [("a", Ty.uint), ("b", Ty.int), ("c", Ty.uint), ("xs", Ty.ref (RefTy.array Ty.uint))]
  | _ => []

/-- The widths of a struct's narrow members, keyed by their path below the
member as `Contract.widths` keys a state variable's (`expandStateTyW`):
`struct Packed { uint8 a; int16 b; uint c; uint8[] xs; }` is `a` at 8, `b`
at 16 and `xs[]` at 8.  Each such member is a `uint` or an `int` in
`structDef`; the elaborator reads this table, nothing below it does. -/
def structWidths : Name -> List (String × Nat)
  | "Packed" => [("a", 8), ("b", 16), ("xs[]", 8)]
  | _ => []

/-- Struct declarations solc refuses ("Identifier already declared"): two
members of one name.  None is in `structDef`, so every struct of the table
has distinct member names (`structDef_nodup`, below); a type that names one is an
elaboration error (`unknownStructMsg`), pinned on `BadDup`. -/
def refusedStructs : List (Name × List (Name × Ty)) :=
  [("BadDup", [("a", Ty.uint), ("a", Ty.bool)])]

/-- The first member name `fs` declares twice. -/
def dupKey? : List (Name × Ty) → Option Name
  | [] => none
  | (k, _) :: rest => if rest.any (·.1 == k) then some k else dupKey? rest

/-- Why the type name `s`, not a struct of `structDef`, is refused: its
declaration repeats a member (`refusedStructs`), or it names nothing. -/
def unknownStructMsg (s : String) : String :=
  match (refusedStructs.find? (·.1 == s)).bind (dupKey? ·.2) with
  | some f => s!"struct {s}: identifier already declared: member {f}"
  | none => unknownTyMsg s

/-! ### The `structDef` termination certificate

`tyRank`-fuelled functions (`SVal.dflt`) and `tyHasMapping` expand a
struct through the `structDef`
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
  | "FixedTriple" => 2
  | "Pair" => 1
  | "FileLevelPair" => 1
  | "S" => 1
  | "Sub" => 1
  | "WithSub" => 2
  | "Inner" => 1
  | "Outer" => 2
  | "Simple" => 1
  | "WithArray" => 1
  | "Triple" => 1
  | "D" => 1
  | "Nest" => 1
  | "Packed" => 1
  | _ => 1

/-- A type's rank: primitives 0, a struct its `structRank`, a dynamic array
and a mapping the rank of the type they expand into, a fixed-size array one
more (its layout recurses into its element, `Evm.sizeF`). -/
def tyRank : Ty -> Nat
  | Ty.prim _ => 0
  | Ty.ref (RefTy.struct n) => structRank n
  | Ty.ref (RefTy.array e) => tyRank e
  | Ty.ref (RefTy.fixed e _) => tyRank e + 1
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
elaborator refuses one — the program does not exist. -/
def tyHasMapping : Ty -> Bool
  | Ty.prim _ => false
  | Ty.ref (RefTy.mapping _ _) => true
  | Ty.ref (RefTy.struct name) => fieldsHaveMapping (structDef name)
  | Ty.ref (RefTy.array elem) => tyHasMapping elem
  | Ty.ref (RefTy.fixed elem _) => tyHasMapping elem
termination_by ty => (tyRank ty, sizeOf ty)
decreasing_by
  · exact Prod.Lex.left _ _ (structDef_rank_lt _)
  all_goals first
    | (apply Prod.Lex.left; simp [tyRank]; done)
    | (apply Prod.Lex.right; simp; omega)

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

/-- No duplicate keys: a layout read through `lookupBy` has one entry per
key (a contract's roots, a struct's members). -/
def nodupKeysB [DecidableEq κ] : List (κ × α) -> Bool
  | [] => true
  | (k, _) :: rest => (lookupBy k rest).isNone && nodupKeysB rest

/-! ### Association-list laws -/

@[simp] theorem lookupBy_setBy_self [DecidableEq κ] (k : κ) (v : α)
    (l : List (κ × α)) : lookupBy k (setBy k v l) = some v := by
  induction l with
  | nil => simp only [setBy, lookupBy, ↓reduceIte]
  | cons hd tl ih =>
      obtain ⟨k', v'⟩ := hd
      by_cases h : k = k' <;> simp only [h, setBy, ↓reduceIte, lookupBy, ih]

theorem lookupBy_setBy_ne [DecidableEq κ] {k k' : κ} (h : k ≠ k')
    (v : α) (l : List (κ × α)) :
    lookupBy k (setBy k' v l) = lookupBy k l := by
  induction l with
  | nil => simp only [setBy, lookupBy, h, ↓reduceIte]
  | cons hd tl ih =>
      obtain ⟨k'', v''⟩ := hd
      by_cases h₂ : k' = k''
      · subst h₂
        simp only [setBy, ↓reduceIte, lookupBy, h]
      · by_cases h₃ : k = k'' <;>
          simp only [h₃, setBy, h₂, ↓reduceIte, lookupBy, ih]

/-- Overwriting the same key twice keeps only the second write
(assoc-list core of KeY `simplifyUpdate1-3`). -/
theorem setBy_setBy_self [DecidableEq κ] (k : κ) (v v' : α)
    (l : List (κ × α)) : setBy k v' (setBy k v l) = setBy k v' l := by
  induction l with
  | nil => simp only [setBy, ↓reduceIte]
  | cons hd tl ih =>
      obtain ⟨k'', v''⟩ := hd
      by_cases h : k = k'' <;> simp only [h, setBy, ↓reduceIte, ih]

/-- A member that `lookupBy` finds is in the list: `age` is a member of `Person`. -/
theorem lookupBy_eq_some_mem [DecidableEq κ] {k : κ} {v : α} :
    ∀ {l : List (κ × α)}, lookupBy k l = some v → (k, v) ∈ l
  | [], h => by simp only [lookupBy, reduceCtorEq] at h
  | (k', v') :: l, h => by
    simp only [lookupBy] at h
    split at h
    · cases h; rename_i hk; subst hk; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookupBy_eq_some_mem h)

end Semantics

/-- **Every struct of the table has distinct member names**: solc refuses
a struct that repeats one (`refusedStructs`, decision 16), and so does the
elaborator, so none is in `structDef`. -/
theorem structDef_nodup (s : Name) : Semantics.nodupKeysB (Semantics.structDef s) = true := by
  unfold Semantics.structDef
  split <;> rfl

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
    -- `ArraySort` (`T[n]`) is the lattice's `array` sort too: its length is in
    -- the name only (`KeySort.array`'s docstring)
    | RefTy.fixed elem _ =>
        if memoryPayload then KeySort.identity else KeySort.array (elem.keySort false)
    | RefTy.mapping key value =>
        KeySort.mapping (if key == .bool then KeySort.bool else KeySort.int)
          (value.keySort false)
end

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
    | fixed _ _ => rfl
    | mapping _ _ => simp [Ty.allowsMemory, RefTy.allowsMemory] at h

/-- `\generic alphaId \extends Identity` (under `\hasMemoryFieldSort`)
binds exactly the memory reference types — the Java's shape-only test,
so an array of mappings is admitted even though `allowsMemory` refuses it. -/
theorem Ty.keySort_memory_le_identity (ty : Ty) :
    (ty.keySort true).le KeySort.identity = ty.isMemoryReferenceType := by
  cases ty with
  | prim p => cases p <;> rfl
  | ref r => cases r <;> rfl

/-- Solidity's ternary modular builtins use an unbounded intermediate. -/
inductive ModOp where
  | addmod | mulmod
  deriving DecidableEq, Repr, Lean.ToExpr

def ModOp.toStr : ModOp → String
  | .addmod => "addmod"
  | .mulmod => "mulmod"

def ModOp.ofName? : String → Option ModOp
  | "addmod" => some .addmod
  | "mulmod" => some .mulmod
  | _ => none

/-- Binary operators of the KeY calculus (`solidityProgramRules.key`):
arithmetic (`addition` .. `modulo`), comparisons (`lessThan` ..
`greaterEqual`) and boolean connectives (`boolEquality`, `boolInequality`,
`logicalAnd`, `logicalOr`).  Then the operators solkey has no taclet for,
all at `uint` only: bitwise `&`, `|`, `^` and the shifts `<<`, `>>`, and the
wrapping arithmetic an `unchecked { … }` block is made of, spelt `+%`, `-%`,
`*%`, `**%` (`band` … `powW`). -/
inductive BinOp where
  | add | sub | mul | pow | div | mod
  | lt | gt | le | ge
  | eqB | neB | and | or
  | band | bor | bxor | shl | shr
  | addW | subW | mulW | powW
  deriving DecidableEq, Repr

namespace BinOp

def isArith : BinOp -> Bool
  | add | sub | mul | pow | div | mod => true
  | band | bor | bxor | shl | shr | addW | subW | mulW | powW => true
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

/-- The Solidity spelling: the one operator table, which the printers write
and the grammar's expanders read back (`ofSym?`). -/
def sym : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .pow => "**" | .div => "/" | .mod => "%"
  | .lt => "<" | .gt => ">" | .le => "<=" | .ge => ">="
  | .eqB => "==" | .neB => "!=" | .and => "&&" | .or => "||"
  | .band => "&" | .bor => "|" | .bxor => "^" | .shl => "<<" | .shr => ">>"
  | .addW => "+%" | .subW => "-%" | .mulW => "*%" | .powW => "**%"

/-- Every operator. -/
def all : List BinOp :=
  [add, sub, mul, pow, div, mod, lt, gt, le, ge, eqB, neB, and, or,
   band, bor, bxor, shl, shr, addW, subW, mulW, powW]

/-- The operator spelt `s`. -/
def ofSym? (s : String) : Option BinOp :=
  all.find? (·.sym == s)

end BinOp

/-- Unary operators: `unaryMinus*` and `logicalNot*` taclets; `~`, the
bitwise complement at `uint`, has none.  `int(u)` and `uint(i)` are solc's
conversions between `uint256` and `int256`, the same 256-bit word read in
two's complement (`2^256 - 1` is `-1`): what a cast between the signed and
unsigned types, a narrowing `int` cast and signed `unchecked` arithmetic
elaborate through (`castCapture`); no solkey taclet. -/
inductive UnOp where
  | neg | not
  | bnot
  | toInt | toUint
  deriving DecidableEq, Repr

def UnOp.sym : UnOp → String
  | .neg => "-" | .not => "!" | .bnot => "~" | .toInt => "int" | .toUint => "uint"

/-- `op` applied to the operand written `a`: `-a`, `!a`, `~a`; the
conversions are written as the casts they come from, `int(a)`, `uint(a)`. -/
def UnOp.show (op : UnOp) (a : String) : String :=
  match op with
  | .toInt | .toUint => s!"{op.sym}({a})"
  | _ => op.sym ++ a

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

/-- The operator the token `t` (`++`, or `−−`, two U+2212) spells, before its
operand (`pre`) or after it. -/
def ofTok? (pre : Bool) : String → Option IncDec
  | "++" => some (if pre then preInc else postInc)
  | "−−" => some (if pre then preDec else postDec)
  | _ => none

end IncDec

/-! ## The five shapes of a type

`Ty` is `prim | ref`, with the reference sorts one level down.  A case split
wants the five source-level shapes at once: `uint x`, `Person p`,
`uint[] xs`, `uint[3] xs`, `mapping(uint => uint) m`. -/

namespace Ty

@[match_pattern, reducible] def struct (n : Name) : Ty := .ref (.struct n)
@[match_pattern, reducible] def array (T : Ty) : Ty := .ref (.array T)
@[match_pattern, reducible] def fixed (T : Ty) (n : Nat) : Ty := .ref (.fixed T n)
@[match_pattern, reducible] def mapping (K : PrimTy) (V : Ty) : Ty := .ref (.mapping K V)

/-- The Solidity spelling: `uint`, `Person[]`, `mapping(uint => bool)`. -/
def toStr : Ty → String
  | .prim p => p.toStr
  | .ref (.struct s) => s
  | .ref (.array T) => T.toStr ++ "[]"
  | .ref (.fixed T n) => s!"{T.toStr}[{n}]"
  | .ref (.mapping K V) => s!"mapping({K.toStr} => {V.toStr})"

instance : ToString Ty := ⟨toStr⟩

end Ty

/-! ## Mapping-free types, well-formed defaults

A storage copy of a type that holds a mapping is rejected by solc, and a
fresh default must be well-formed.  `tyHasMapping` and `defaultOk` answer
these by well-founded recursion through `structDef`, which the kernel
cannot evaluate; `mapFree` and `defaultOkS` answer them structurally, so
their proofs are `Eq.refl`, from a list of the structs checked once
(`mapFree_structDef` in `Semantics/Storage.lean`). -/

/-- The structs of `structDef` that hold no mapping. -/
def mapFreeStructs : List Name :=
  ["Token", "Account", "Person", "Basket", "TokenBucket", "Toggle", "FixedTriple", "Pair", "FileLevelPair", "S",
   "Sub", "WithSub", "Inner", "Outer", "Simple", "WithArray", "Triple", "D", "Nest",
   "Packed"]

/-- `T` holds no mapping: `Person[]` does not, `mapping(uint => uint)` does. -/
def Ty.mapFree : Ty → Bool
  | .prim _ => true
  | .ref (.mapping ..) => false
  | .ref (.struct s) => s ∈ mapFreeStructs
  | .ref (.array e) => e.mapFree
  | .ref (.fixed e _) => e.mapFree

/-- A member of a struct that holds no mapping holds none: what a memory
path's type inherits from its receiver's (`MPath.memOk`). -/
theorem Ty.mapFree_field {s f : Name} {T : Ty} (hs : (Ty.ref (.struct s)).mapFree = true)
    (h : Semantics.lookupBy f (Semantics.structDef s) = some T) : T.mapFree = true := by
  have hall : ∀ s ∈ mapFreeStructs, ∀ p ∈ Semantics.structDef s, p.2.mapFree = true := by
    decide
  simp only [Ty.mapFree, decide_eq_true_eq] at hs
  exact hall s hs (f, T) (Semantics.lookupBy_eq_some_mem h)

/-- The structs whose fresh default is well-formed: every struct of the
table.  A struct with a repeated member name would not be (its second row
has the wrong type for what the name looks up to), and solc refuses one
(`refusedStructs`). -/
def defaultOkStructs : List Name :=
  ["Token", "Account", "Person", "Wallet", "Basket", "Ledger", "LedgerUse", "TokenBucket",
   "Toggle", "FixedTriple", "Pair", "FileLevelPair", "S", "Sub", "WithSub", "Inner", "Outer", "Simple",
   "WithArray", "Triple", "D", "Nest", "Packed"]

/-- `T`'s fresh default is well-formed: what `values.push();` and
`Person memory m;` need. -/
def Ty.defaultOkS : Ty → Bool
  | .prim _ => true
  | .ref (.struct s) => s ∈ defaultOkStructs
  | .ref (.array _) => true
  | .ref (.fixed e _) => e.defaultOkS
  | .ref (.mapping _ v) => v.defaultOkS

/-! ## Operators at primitive types -/

/-- The primitive operand type an operator accepts: arithmetic and
comparisons on numbers, `&&`/`||` on booleans, `==`/`!=` on either. -/
def BinOp.accepts : BinOp → PrimTy → Bool
  | .and, p | .or, p => p == .bool
  | .eqB, _ | .neB, _ => true
  -- solc takes an unsigned exponent, and an operator here is applied at one
  -- type: `**` is `uint ** uint`
  | .pow, p => p == .uint
  -- bitwise and `>>` at either: at `int` solc reads them in two's complement
  -- (`uintBitwise`, an arithmetic `>>`); `<<` and wrapping arithmetic at `uint`
  | .band, p | .bor, p | .bxor, p | .shr, p => p.isNumeric
  | .shl, p => p == .uint
  | .addW, p | .subW, p | .mulW, p | .powW, p => p == .uint
  | _, p => p.isNumeric

/-- The result type at operand type `p`: `a + b` on `uint` is a `uint`,
`a < b` a `bool`. -/
def BinOp.ret (op : BinOp) (p : PrimTy) : PrimTy :=
  if op.isArith then p else .bool

def UnOp.accepts : UnOp → PrimTy → Bool
  -- `-x` at `int` only, as solc: it rejects unary minus on an unsigned type
  | .neg, p => p == .int
  | .not, p => p == .bool
  | .bnot, p => p == .uint
  | .toInt, p => p == .uint
  | .toUint, p => p == .int

/-- `-x` and `~x` keep their type, `!b` is a `bool`, `int(u)` an `int` and
`uint(i)` a `uint`. -/
def UnOp.ret : UnOp → PrimTy → PrimTy
  | .neg, p => p
  | .not, _ => .bool
  | .bnot, p => p
  | .toInt, _ => .int
  | .toUint, _ => .uint

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

/- Not a parameter to specialize on: `dl!{ … }` and `sol{ … }` evaluate a call
of the elaborator at the file's instance, and specializing it there compiles
the whole elaborator again at every line (half a second each). -/
attribute [nospecialize] FreshNames

/-- The `k`-th fresh variable of each kind is a prefix and `k`.  The four
prefixes must be distinct identifiers that do not end in a digit.  A loop's
flags keep solkey's names (`brk1`, `cnt2`, `ret3`, `first4`: `lowerLoops`),
and push-source captures use `source1`. These fixed prefixes must also be
distinct from the four configurable prefixes. Custom prefixes must avoid
contract roots; `FreshNames.clashes` checks explicit table aliases only. -/
def FreshNames.ofPrefixes (se sp ie mv : String) : FreshNames where
  name b k :=
    let pre := if b = "se" then se else if b = "sp" then sp else if b = "ie" then ie
      else if b = "mv" then mv else b
    s!"{pre}{k}"
  parse s :=
    let stem := s.takeWhile (!·.isDigit)
    let digits := s.drop stem.length
    if digits.isEmpty || !digits.all (·.isDigit) then none
    else ([("se", se), ("sp", sp), ("ie", ie), ("mv", mv), ("brk", "brk"), ("cnt", "cnt"),
        ("ret", "ret"), ("first", "first"), ("source", "source")].find? (·.2 == stem)).map
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

/-- solc's mutabilities, the most restrictive first.  `payable` is
`nonpayable` here: a callee's booking of `msg.value` is its caller's. -/
inductive Mutability where
  | pure
  | view
  | nonpayable
  deriving DecidableEq, Repr

end Solidity
