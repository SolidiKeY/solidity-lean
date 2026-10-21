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
    else if s == "byte" then ": `byte` is `bytes1` since solc 0.8"
    else if s.startsWith "bytes" || s == "string" then
      ": `bytes1` … `bytes32`, `bytes` and `string` stand where a narrow integer may, not here"
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

/-! ### A contract's own structs: names that spell their members

A contract's struct that is not the table's (`docs/semantic-gaps.md`,
"Struct table") is the table's struct whose name spells its members:
`Pair{a:uint;b:bool}`, each member's type as Solidity writes it without
spaces (a narrow `uint8` as written, a table struct by its name, a contract
struct by its own such name, `T[]`, `T[n]`, `mapping(K=>V)`).  The table's
last arm decodes such a name (`structDefEnc`) and keeps the members only if
they pass the table's certificates, so every theorem about the table holds
of them by that check.  The decoder is structural (fuel: the name's length),
so the kernel reduces it. -/

namespace StructEnc

def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'

/-- The leading identifier and what follows it. -/
def ident : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if isIdChar c then match ident cs with | (a, b) => (c :: a, b) else ([], c :: cs)

/-- The leading digits and what follows them. -/
def digits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if c.isDigit then match digits cs with | (a, b) => (c :: a, b) else ([], c :: cs)

def natOf (ds : List Char) : Nat := ds.foldl (fun n c => 10 * n + (c.toNat - 48)) 0

/-- A member list up to the `}` that closes it at depth `d`, that `}`
included, and what follows. -/
def block : Nat → List Char → Option (List Char × List Char)
  | _, [] => none
  | d, c :: cs =>
    let d' : Option Nat :=
      if c == '{' then some (d + 1)
      else if c == '}' then (match d with | 0 => none | e + 1 => some e)
      else some d
    match d' with
    | none => some ([c], cs)
    | some e =>
      match block e cs with
      | some (a, b) => some (c :: a, b)
      | none => none

/-- A primitive type by its name: `PrimTy.ofName?`'s, a narrow `uintN`,
`intN`, or a `bytesN`, a `uint` (its width and marker are `structWidths`'s). -/
def primOf (n : List Char) : Option PrimTy :=
  match PrimTy.ofName? (String.mk n) with
  | some p => some p
  | none =>
    match n with
    | 'u' :: 'i' :: 'n' :: 't' :: ds@(_ :: _) => if ds.all Char.isDigit then some .uint else none
    | 'i' :: 'n' :: 't' :: ds@(_ :: _) => if ds.all Char.isDigit then some .int else none
    | 'b' :: 'y' :: 't' :: 'e' :: 's' :: ds@(_ :: _) =>
      if ds.all Char.isDigit then some .uint else none
    | _ => none

/-- `bytes` and `string`, each a `bytes1[]`: a `uint[]` 8 bits wide. -/
def dynBytes (n : List Char) : Bool := n == "bytes".data || n == "string".data

/-- What follows the `)` that closes depth `d` (a function type's
parameter or return list). -/
def closeParen : Nat → List Char → Option (List Char)
  | _, [] => none
  | d, c :: cs =>
    if c == ')' then (match d with | 0 => some cs | e + 1 => closeParen e cs)
    else if c == '(' then closeParen (d + 1) cs
    else closeParen d cs

/-- `cs` after the prefix `p`, if it starts with it. -/
def dropPrefix? : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | p :: ps, c :: cs => if p == c then dropPrefix? ps cs else none
  | _ :: _, [] => none

/-- What follows a function type's spelling after its `function(`:
`uint)external returns(uint)` less `uint)`, `external`, `returns(uint)`. -/
def fnRest (cs : List Char) : Option (List Char) := do
  let r ← closeParen 0 cs
  let r := (dropPrefix? "external".data r).getD r
  match dropPrefix? "returns(".data r with
  | some r' => closeParen 0 r'
  | none => some r

/-- `string=>` or `bytes=>` at the head of a mapping: what follows. -/
def hashKey? (cs : List Char) : Option (List Char) :=
  (dropPrefix? "string=>".data cs).orElse fun _ => dropPrefix? "bytes=>".data cs

/-- The array suffixes `[]`, `[n]` after a type. -/
def suffixes : Nat → Ty → List Char → Ty × List Char
  | 0, T, cs => (T, cs)
  | k + 1, T, '[' :: ']' :: cs => suffixes k (.ref (.array T)) cs
  | k + 1, T, '[' :: cs =>
    match digits cs with
    | (ds@(_ :: _), ']' :: rest) => suffixes k (.ref (.fixed T (natOf ds))) rest
    | _ => (T, '[' :: cs)
  | _ + 1, T, cs => (T, cs)

/-- A member's type, and what follows it. -/
def parseTy : Nat → List Char → Option (Ty × List Char)
  | 0, _ => none
  | k + 1, 'm' :: 'a' :: 'p' :: 'p' :: 'i' :: 'n' :: 'g' :: '(' :: cs =>
    -- a byte string as a key: its `keccak256`, a `uint`
    let key : Option (PrimTy × List Char) := match hashKey? cs with
      | some cs' => some (.uint, cs')
      | none => match parseTy k cs with
        | some (.prim K, '=' :: '>' :: cs') => some (K, cs')
        | _ => none
    match key with
    | some (K, cs') =>
      match parseTy k cs' with
      | some (V, ')' :: rest) => some (suffixes rest.length (.ref (.mapping K V)) rest)
      | _ => none
    | none => none
  -- a function type: its value a `uint` (`fnTy?`)
  | _ + 1, 'f' :: 'u' :: 'n' :: 'c' :: 't' :: 'i' :: 'o' :: 'n' :: '(' :: cs =>
    match fnRest cs with
    | some rest => some (suffixes rest.length (.prim .uint) rest)
    | none => none
  | k + 1, cs =>
    match ident cs with
    | ([], _) => none
    | (n, '{' :: rest) =>
      match block 0 rest with
      | some (body, rest') =>
        some (suffixes rest'.length (.ref (.struct (String.mk (n ++ '{' :: body)))) rest')
      | none => none
    | (n, rest) =>
      let T : Ty := match primOf n with
        | some p => .prim p
        | none => if dynBytes n then .ref (.array (.prim .uint)) else .ref (.struct (String.mk n))
      some (suffixes rest.length T rest)

/-- The members `f:T;…}`. -/
def parseFields : Nat → List Char → Option (List (Name × Ty))
  | 0, _ => none
  | k + 1, cs =>
    match ident cs with
    | (f@(_ :: _), ':' :: rest) =>
      match parseTy k rest with
      | some (T, ['}']) => some [(String.mk f, T)]
      | some (T, ';' :: rest') => (parseFields k rest').map ((String.mk f, T) :: ·)
      | _ => none
    | _ => none

/-- The members a name spells, if it spells some: `S{…}`. -/
def decode (s : Name) : Option (List (Name × Ty)) :=
  match ident s.data with
  | (_ :: _, '{' :: body) => parseFields body.length body
  | _ => none

end StructEnc

/-- A name that spells its members (`StructEnc`). -/
def isEnc (s : Name) : Bool := s.data.contains '{'

/-- The name a struct is written by: the part before `{`. -/
def structDisplay (s : Name) : Name := String.mk (s.data.takeWhile (· != '{'))

/-- The bound on every struct's rank: the fuel of the defaults (`rankBound`). -/
def structRankCap : Nat := 16

/-- A spelled struct's rank: its braces and brackets, above the table's
(at most 4), capped.  A nested struct's name is a part of it with fewer
braces, a fixed-size array a bracket more. -/
def encRank (s : Name) : Nat :=
  min (4 + (s.data.filter fun c => c == '{' || c == '[').length) structRankCap

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
  | s => encRank s

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
  unfold structRank; split <;> first
    | decide
    | exact Nat.lt_min.mpr ⟨Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right 4 _), by decide⟩

end Semantics

/-! ## Mapping-free types, well-formed defaults

A storage copy of a type that holds a mapping is rejected by solc, and a
fresh default must be well-formed.  `tyHasMapping` and `defaultOk` answer
these by well-founded recursion through `structDef`, which the kernel
cannot evaluate; `mapFree` and `defaultOkS` answer them structurally, so
their proofs are `Eq.refl`, from a list of the table's structs checked once
(`mapFree_structDef`), and for a spelled struct (`StructEnc`) from its
members, which the table keeps only if they agree (`structDefEnc`). -/

/-- The structs of the table that hold no mapping. -/
def mapFreeStructs : List Name :=
  ["Token", "Account", "Person", "Basket", "TokenBucket", "Toggle", "FixedTriple", "Pair", "FileLevelPair", "S",
   "Sub", "WithSub", "Inner", "Outer", "Simple", "WithArray", "Triple", "D", "Nest",
   "Packed"]

/-- `T` holds no mapping, a struct as `st` says. -/
def Ty.mapFreeWith (st : Name → Bool) : Ty → Bool
  | .prim _ => true
  | .ref (.mapping ..) => false
  | .ref (.struct s) => st s
  | .ref (.array e) => e.mapFreeWith st
  | .ref (.fixed e _) => e.mapFreeWith st

/-- A struct holds no mapping: one of `mapFreeStructs`, or a spelled one
whose members hold none, with fuel `k`. -/
def structMapFreeF : Nat → Name → Bool
  | 0, s => s ∈ mapFreeStructs
  | k + 1, s => s ∈ mapFreeStructs ||
      (Semantics.isEnc s &&
        match Semantics.StructEnc.decode s with
        | some fs => fs.all fun f => f.2.mapFreeWith (structMapFreeF k)
        | none => false)

/-- A struct holds no mapping (fuel: its name's length, which bounds its
nesting). -/
def structMapFree (s : Name) : Bool := structMapFreeF s.length s

/-- `T` holds no mapping: `Person[]` does not, `mapping(uint => uint)` does. -/
def Ty.mapFree : Ty → Bool
  | .prim _ => true
  | .ref (.mapping ..) => false
  | .ref (.struct s) => structMapFree s
  | .ref (.array e) => e.mapFree
  | .ref (.fixed e _) => e.mapFree

/-- The table's structs whose fresh default is well-formed: every struct of
the table.  A struct with a repeated member name would not be (its second row
has the wrong type for what the name looks up to), and solc refuses one
(`refusedStructs`). -/
def defaultOkStructs : List Name :=
  ["Token", "Account", "Person", "Wallet", "Basket", "Ledger", "LedgerUse", "TokenBucket",
   "Toggle", "FixedTriple", "Pair", "FileLevelPair", "S", "Sub", "WithSub", "Inner", "Outer", "Simple",
   "WithArray", "Triple", "D", "Nest", "Packed"]

/-- A struct whose fresh default is well-formed: one of `defaultOkStructs`, or
a spelled one (the table keeps its members only if they are distinct and
well-formed, `structDefEnc`). -/
def structOk (s : Name) : Bool := s ∈ defaultOkStructs || Semantics.isEnc s

/-- `T`'s default is well-formed all the way down: a struct `structOk`
admits, and arrays and mappings of such. -/
def Ty.okDeep : Ty → Bool
  | .prim _ => true
  | .ref (.struct s) => structOk s
  | .ref (.array E) => E.okDeep
  | .ref (.fixed E _) => E.okDeep
  | .ref (.mapping _ V) => V.okDeep

namespace Semantics

/-- The certificates a spelled struct's members must pass for the table to
keep them: some members, of rank below the struct's, distinct, well-formed
all the way down, and holding no mapping if the struct claims none. -/
def encFieldsOk (s : Name) (fs : List (Name × Ty)) : Bool :=
  !fs.isEmpty && decide (fieldsRank fs < structRank s) && nodupKeysB fs &&
    fs.all (fun f => f.2.okDeep) && (!structMapFree s || fs.all fun f => f.2.mapFree)

/-- A spelled struct's members, if they pass `encFieldsOk`; else none, as an
unknown name has. -/
def structDefEnc (s : Name) : List (Name × Ty) :=
  match StructEnc.decode s with
  | some fs => if encFieldsOk s fs then fs else []
  | none => []

/-- What `List.all` says of a member (without `funext`, which
`List.all_eq_true` uses). -/
theorem all_mem {p : α → Bool} : ∀ {l : List α}, l.all p = true → ∀ x ∈ l, p x = true
  | [], _, _, hx => nomatch hx
  | y :: l, h, x, hx => by
    have h' : (p y && l.all p) = true := h
    rw [Bool.and_eq_true] at h'
    cases hx with
    | head => exact h'.1
    | tail _ hx => exact all_mem h'.2 x hx

theorem structDefEnc_ok (s : Name) :
    structDefEnc s = [] ∨ encFieldsOk s (structDefEnc s) = true := by
  unfold structDefEnc
  split
  · split
    · exact Or.inr (by assumption)
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- Struct definitions of the ported contracts.

The trailing catch-all reads a contract's own struct, whose name spells its
members (`StructEnc`, `structDefEnc`).  Any other name has zero fields, so
`SVal.dflt` builds an empty node for it instead of being `undef`: the
elaborators refuse a type that names no struct (`unknownStructMsg`) and a
declaration whose members the check would drop (`expandStructs`), so no
program meets one. -/
def structDef (s : Name) : List (Name × Ty) :=
  match s with
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
  | _ => structDefEnc s

namespace StructEnc

/-- `l` split at `sep` where no bracket is open. -/
def splitTop (sep : Char) : Nat → List Char → List Char → List (List Char)
  | _, acc, [] => [acc.reverse]
  | d, acc, c :: cs =>
    if d == 0 && c == sep then acc.reverse :: splitTop sep 0 [] cs
    else
      let d' := if c == '{' || c == '(' || c == '[' then d + 1
        else if c == '}' || c == ')' || c == ']' then d - 1 else d
      splitTop sep d' (c :: acc) cs

/-- The width of a narrow type's name, `uint8` is `8`. -/
def narrowWidth (n : List Char) : Option Nat :=
  let w (ds : List Char) : Option Nat :=
    if !ds.isEmpty && ds.all Char.isDigit && natOf ds < 256 then some (natOf ds) else none
  match n with
  | 'u' :: 'i' :: 'n' :: 't' :: ds => w ds
  | 'i' :: 'n' :: 't' :: ds => w ds
  | _ => none

/-- The rows a value type adds at its own position, as `valueRows?`
(`Syntax.lean`) gives them: a narrow integer's width, a `bytesN`'s width
below 256 bits and its marker `#bytes`, a function type's marker, an
`address`'s. -/
def valueRowsOf (t : List Char) : List (String × Nat) :=
  match t with
  | 'f' :: 'u' :: 'n' :: 'c' :: 't' :: 'i' :: 'o' :: 'n' :: '(' :: _ => [("#" ++ String.mk t, 0)]
  | ['a', 'd', 'd', 'r', 'e', 's', 's'] => [("#address", 20)]
  | 'b' :: 'y' :: 't' :: 'e' :: 's' :: ds =>
    if !ds.isEmpty && ds.all Char.isDigit && 1 ≤ natOf ds && natOf ds ≤ 32 then
      (if natOf ds < 32 then [("", 8 * natOf ds)] else []) ++ [("#bytes", natOf ds)]
    else []
  | _ => (narrowWidth t).toList.map fun n => ("", n)

/-- The narrow positions of a spelled type, keyed as `structWidths` keys them. -/
def shapeOf : Nat → List Char → List (String × Nat)
  | 0, _ => []
  | k + 1, t =>
    if t.getLast? == some ']' then
      let inner := ((t.reverse.dropWhile (· != '[')).drop 1).reverse
      (shapeOf k inner).map fun (p, n) => ("[]" ++ p, n)
    else
      match t with
      | 'm' :: 'a' :: 'p' :: 'p' :: 'i' :: 'n' :: 'g' :: '(' :: cs =>
        match splitTop '=' 0 [] cs.dropLast with
        | [kt, '>' :: vt] =>
          (if dynBytes kt then [("{}#hash", 1)] else
            (valueRowsOf kt).map fun (p, n) => ("{}" ++ p, n)) ++
            (shapeOf k vt).map fun (p, n) => ("[]" ++ p, n)
        | _ => []
      | _ =>
        if t == "string".data then [("[]", 8), ("[]#bytes", 1), ("#string", 1)]
        else if dynBytes t then [("[]", 8), ("[]#bytes", 1)] else valueRowsOf t

/-- A spelled struct's narrow members (`structWidths`). -/
def widths (s : Name) : List (String × Nat) :=
  match ident s.data with
  | (_ :: _, '{' :: body) =>
    (splitTop ';' 0 [] body.dropLast).flatMap fun m =>
      match splitTop ':' 0 [] m with
      | [f, t] => (shapeOf t.length t).map fun (p, n) => (String.mk f ++ p, n)
      | _ => []
  | _ => []

end StructEnc

/-- The widths of a struct's narrow members, keyed by their path below the
member as `Contract.widths` keys a state variable's (`expandStateTyW`):
`struct Packed { uint8 a; int16 b; uint c; uint8[] xs; }` is `a` at 8, `b`
at 16 and `xs[]` at 8.  Each such member is a `uint` or an `int` in
`structDef`; the elaborator reads this table, nothing below it does. -/
def structWidths : Name -> List (String × Nat)
  | "Packed" => [("a", 8), ("b", 16), ("xs[]", 8)]
  | s => StructEnc.widths s

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


/-- **The certificate.** Every field of a struct outranks nothing: its
rank is strictly below the struct's own.  Checked by `decide` against the
concrete table, so adding a struct whose fields are too deep for its
`structRank` row fails here; a spelled struct's members pass it by
`structDefEnc`'s check. -/
theorem structDef_rank_lt (n : Name) :
    fieldsRank (structDef n) < structRank n := by
  unfold structDef
  split
  case h_24 =>
    rcases structDefEnc_ok n with h | h
    · rw [h]; exact structRank_pos _
    · simp only [encFieldsOk, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1.1.2
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

/-- A property of every struct's members: of the table's, checked once by
`decide`, and of a spelled one's, from `structDefEnc`. -/
theorem structDef_rec {P : Name → List (Name × Ty) → Prop} (s : Name)
    (htab : ∀ t ∈ defaultOkStructs, P t (Semantics.structDef t))
    (henc : P s (Semantics.structDefEnc s)) : P s (Semantics.structDef s) := by
  unfold Semantics.structDef
  split
  case h_24 => exact henc
  all_goals exact htab _ (by decide)

/-- **Every struct of the table has distinct member names**: solc refuses
a struct that repeats one (`refusedStructs`, decision 16), and so does the
elaborator, so none is in `structDef`. -/
theorem structDef_nodup (s : Name) : Semantics.nodupKeysB (Semantics.structDef s) = true := by
  refine structDef_rec (P := fun _ fs => Semantics.nodupKeysB fs = true) s (by decide) ?_
  rcases Semantics.structDefEnc_ok s with h | h
  · rw [h]; rfl
  · simp only [Semantics.encFieldsOk, Bool.and_eq_true] at h
    exact h.1.1.2

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

/-- The builtins that hash a memory byte string whole, by the function they
compute (`HashKind.apply`, `Semantics/Heap.lean`; `docs/semantic-gaps.md`,
"Hashing and the ABI"): `keccak256`, the precompiles `sha256` and
`ripemd160`, and `ecrecover`, whose bytes are its four arguments' ABI words. -/
inductive HashKind where
  | keccak | sha256 | ripemd160 | ecrecover
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- The builtin's name, as Solidity spells it. -/
def HashKind.toStr : HashKind → String
  | .keccak => "keccak256"
  | .sha256 => "sha256"
  | .ripemd160 => "ripemd160"
  | .ecrecover => "ecrecover"

def HashKind.ofName? : String → Option HashKind
  | "keccak256" => some .keccak
  | "sha256" => some .sha256
  | "ripemd160" => some .ripemd160
  | "ecrecover" => some .ecrecover
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
  | .ref (.struct s) => Semantics.structDisplay s
  | .ref (.array T) => T.toStr ++ "[]"
  | .ref (.fixed T n) => s!"{T.toStr}[{n}]"
  | .ref (.mapping K V) => s!"mapping({K.toStr} => {V.toStr})"

instance : ToString Ty := ⟨toStr⟩

end Ty

/-! ## Mapping-free types, well-formed defaults: the table's certificates -/

/-- The members of a struct without mappings are without mappings too. -/
theorem mapFree_structDef (s : Name) (hs : structMapFree s = true) :
    ∀ fT ∈ Semantics.structDef s, fT.2.mapFree = true := by
  refine structDef_rec (P := fun t fs => structMapFree t = true → ∀ fT ∈ fs, fT.2.mapFree = true)
    s (by decide) ?_ hs
  · intro hs
    rcases Semantics.structDefEnc_ok s with h | h
    · rw [h]; intro _ hm; cases hm
    · simp only [Semantics.encFieldsOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
      rcases h.2 with h' | h'
      · rw [hs] at h'; cases h'
      · exact Semantics.all_mem h'

/-- The members of a struct are well-formed all the way down. -/
theorem struct_okDeep {s : Name} (_h : structOk s = true) :
    ∀ nt ∈ Semantics.structDef s, nt.2.okDeep = true := by
  refine structDef_rec (P := fun _ fs => ∀ nt ∈ fs, nt.2.okDeep = true) s (by decide) ?_
  rcases Semantics.structDefEnc_ok s with h | h
  · rw [h]; intro _ hm; cases hm
  · simp only [Semantics.encFieldsOk, Bool.and_eq_true] at h
    exact Semantics.all_mem h.1.2

/-- A member of a struct that holds no mapping holds none: what a memory
path's type inherits from its receiver's (`MPath.memOk`). -/
theorem Ty.mapFree_field {s f : Name} {T : Ty} (hs : (Ty.ref (.struct s)).mapFree = true)
    (h : Semantics.lookupBy f (Semantics.structDef s) = some T) : T.mapFree = true := by
  exact mapFree_structDef s hs (f, T) (Semantics.lookupBy_eq_some_mem h)

/-- `T`'s fresh default is well-formed: what `values.push();` and
`Person memory m;` need. -/
def Ty.defaultOkS : Ty → Bool
  | .prim _ => true
  | .ref (.struct s) => structOk s
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
