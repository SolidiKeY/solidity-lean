import Solidity.AST

/-!
# Executable state semantics

The Lean analogue of the KeY state layer
(`structRules.key`, `memoryRules.key`, `structMemoryRules.key`,
`netHeader.key`): a concrete interpreter for statements and expressions
over a storage tree, an identity-indexed memory heap, local bindings, and
the `net` payment ledger. It gives meaning to `SolidityJudgment`
(`sol!{ < stmts > (post) }`), so the ported KeY taclet tests can be proved
by evaluation.

Semantic conventions mirrored from KeY:
- storage assignment copies by value (`save`/`select`/`store`),
  memory assignment aliases identities, cross-domain assignments deep-copy
  (`copySt`/`copyMem`, see `docs/copyStMem.md`);
- array reads/writes out of bounds revert; `pop()` on an empty array
  reverts; `/` and `%` revert on a zero divisor; a failing `assert`
  reverts;
- `a.transfer(v)` books `net(a) := net(a) - v` with no callback;
- in the postcondition, `net(a)` reads the ledger.

Semantic conventions mirrored from solc (where KeY was more liberal;
see `docs/solc-alignment.md`):
- arithmetic is **checked** (solc ≥ 0.8): an `add`/`sub`/`mul`/`pow`/
  `div`/`mod`/`++`/`--`/compound-assignment result outside its type's
  range (`uint` = `uint256`, `int` = `int256`) reverts, the executable
  image of `Panic(0x11)` (`checkArith`);
- an assignment evaluates its **right-hand side before resolving the
  left-hand side**, and `++`/`--` and `op=` resolve their l-value
  exactly **once** (`readLoc`/`writeLoc`) — solc's code generation
  order for assignments in both the legacy and the IR pipeline;
- a storage-to-storage copy of a type containing a (nested) mapping is
  stuck: solc ≥ 0.7 rejects such assignments at compile time
  (`tyHasMapping`); `delete` keeps its mapping-preserving behavior;
- `a.transfer(v)` reverts unless the contract's own funds
  (`State.selfBalance`) cover `v`, and debits them — the EVM's
  value-transfer balance check.

The interpreter is total: Lean checks termination of every function.
Statement execution is structurally recursive (statements never spawn
statements — `Stmt` has no loops, and the push-assignment forms delegate
to the non-recursive `execAssign`); expression evaluation terminates on
the measure `4 * WrappedExpr.size + rank` (see the mutual block below);
the memory→storage copy terminates on the visited-set complement
`rem` (`copyMToSt`), and the storage→memory copy is structural.
-/

namespace Solidity
namespace Semantics

/-- Primitive run-time values — KeY `Prim \extends StValue, MemValue`
(`solidityDLHeader.key`): the values shared by storage and memory. -/
inductive PrimVal where
  | int (v : Int)
  | bool (b : Bool)
  deriving Repr, DecidableEq

/-- Stack values *are* primitive values: KeY gives primitive-typed
program variables the `Prim` subsorts directly, with no separate stack
sort. `Value` stays as the interpreter-facing name. -/
abbrev Value := PrimVal

namespace Value
export PrimVal (int bool)
end Value

/-- Storage values: the tree model of `structRules.key`. KeY
`Prim, Struct \extends StValue` — `prim` embeds the shared primitives,
the node constructors are the `Struct` side. Mapping nodes carry the
default value for absent keys. -/
inductive SVal where
  | prim (p : PrimVal)
  | struct (fields : List (Name × SVal))
  | array (elems : List SVal)
  | map (entries : List (Int × SVal)) (dflt : SVal)
  deriving Repr

namespace SVal
@[match_pattern] abbrev int (v : Int) : SVal := .prim (.int v)
@[match_pattern] abbrev bool (b : Bool) : SVal := .prim (.bool b)
end SVal

/-- Memory slot values — KeY `Prim, Identity \extends MemValue`
(`memoryHeader.key`): primitives inline, references by identity. -/
inductive MVal where
  | prim (p : PrimVal)
  | ref (id : Nat)
  deriving Repr, DecidableEq

namespace MVal
@[match_pattern] abbrev int (v : Int) : MVal := .prim (.int v)
@[match_pattern] abbrev bool (b : Bool) : MVal := .prim (.bool b)
end MVal

/-- Memory objects, one per identity (`memoryRules.key`). -/
inductive MObj where
  | struct (fields : List (Name × MVal))
  | array (elems : List MVal)
  deriving Repr

/-- One step of a storage path: a field or an `at(i)` selector
(array index or mapping key). -/
inductive Seg where
  | field (name : Name)
  | at (i : Int)
  deriving Repr, DecidableEq

/-- Local bindings: stack values, storage path aliases, memory
references. -/
inductive Binding where
  | val (v : Value)
  | spath (root : Name) (segs : List Seg)
  | mref (id : Nat)
  deriving Repr, DecidableEq

structure State where
  storage : List (Name × SVal)
  heap : List (Nat × MObj) := []
  nextId : Nat := 0
  env : List (Name × Binding) := []
  net : List (Int × Int) := []
  /-- The contract's own funds (`address(this).balance`): `transfer`
  reverts when the amount exceeds this and debits it otherwise — the
  EVM's value-transfer balance check that solc-compiled `transfer`
  inherits. Example stores that exercise `transfer` start it high
  enough for their payments. -/
  selfBalance : Int := 0
  deriving Repr

inductive Halt where
  | revert
  | stuck
  deriving Repr, DecidableEq, Inhabited

abbrev Res (α : Type) := Except Halt α

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
/-- Default storage value of a type (`delete`, fresh array elements,
mapping defaults). -/
def defaultForTy : Ty -> SVal
  | Ty.bool => SVal.bool false
  | Ty.uint => SVal.int 0
  | Ty.int => SVal.int 0
  | Ty.ref (RefTy.struct name) => SVal.struct (defaultForFields (structDef name))
  | Ty.ref (RefTy.array _) => SVal.array []
  | Ty.ref (RefTy.mapping _ value) => SVal.map [] (defaultForTy value)
termination_by ty => (tyRank ty, sizeOf ty)
decreasing_by
  · exact Prod.Lex.left _ _ (structDef_rank_lt _)
  · apply Prod.Lex.right; simp; omega

def defaultForFields : List (Name × Ty) -> List (Name × SVal)
  | [] => []
  | (n, t) :: rest => (n, defaultForTy t) :: defaultForFields rest
termination_by l => (fieldsRank l, sizeOf l)
decreasing_by
  all_goals (apply lex_le_lt
             · simp only [fieldsRank]; omega
             · simp; omega)
end

def defaultForRef (ref : RefTy) : SVal :=
  defaultForTy (Ty.ref ref)

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

/-- Shape-preserving default (`defaultOf` on the current value):
`delete` resets primitives, empties arrays, and recurses into struct
fields — but leaves mappings untouched (entries and default), the
Solidity `delete` semantics solkey implements with the lazy `delNode`
marker (`selectStDelNodeMap` reads mapping members through to the
original). A direct `delete` on a mapping is a solc compile error, so
the no-op `map` arm is unreachable from real programs. -/
def SVal.defaultOf : SVal -> SVal
  | SVal.int _ => SVal.int 0
  | SVal.bool _ => SVal.bool false
  | SVal.struct fields => SVal.struct (defaultOfFields fields)
  | SVal.array _ => SVal.array []
  | SVal.map entries dflt => SVal.map entries dflt
where defaultOfFields : List (Name × SVal) -> List (Name × SVal)
  | [] => []
  | (name, v) :: rest => (name, v.defaultOf) :: defaultOfFields rest

/-! ## Association-list helpers -/

def lookupBy [DecidableEq κ] (k : κ) : List (κ × α) -> Option α
  | [] => none
  | (k', v) :: rest => if k = k' then some v else lookupBy k rest

def setBy [DecidableEq κ] (k : κ) (v : α) : List (κ × α) -> List (κ × α)
  | [] => [(k, v)]
  | (k', v') :: rest =>
      if k = k' then (k, v) :: rest else (k', v') :: setBy k v rest

/-! ## Storage find / save -/

def SVal.find : SVal -> List Seg -> Res SVal
  | v, [] => .ok v
  | SVal.struct fields, Seg.field name :: rest =>
      match lookupBy name fields with
      | some v => v.find rest
      | none => .error .stuck
  | SVal.array elems, Seg.at i :: rest =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then
        (elems.get ⟨i.toNat, h.2⟩).find rest
      else .error .revert
  -- `a.length`: solkey's suites assert array lengths directly
  -- (`assert(values.length == 3)`), and the parser gives `.length` a
  -- `Seg.field`, so it has to be answered here rather than by the struct
  -- arm above — an array is not a struct with a `length` member.
  | SVal.array elems, Seg.field "length" :: rest =>
      (SVal.int elems.length).find rest
  | SVal.map entries dflt, Seg.at i :: rest =>
      match lookupBy i entries with
      | some v => v.find rest
      | none => dflt.find rest
  -- The shape mismatches, enumerated rather than left to a wildcard: a
  -- primitive under any selector, a struct under `at`, an array under a
  -- field other than the `length` arm above, a mapping under a field.
  | SVal.prim _, _ :: _ => .error .stuck
  | SVal.struct _, Seg.at _ :: _ => .error .stuck
  | SVal.array _, Seg.field _ :: _ => .error .stuck
  | SVal.map _ _, Seg.field _ :: _ => .error .stuck

def SVal.save : SVal -> List Seg -> SVal -> Res SVal
  | _, [], new => .ok new
  | SVal.struct fields, Seg.field name :: rest, new =>
      match lookupBy name fields with
      | some old => do
          let updated ← old.save rest new
          .ok (SVal.struct (setBy name updated fields))
      | none => .error .stuck
  | SVal.array elems, Seg.at i :: rest, new =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then do
        let updated ← (elems.get ⟨i.toNat, h.2⟩).save rest new
        .ok (SVal.array (elems.set i.toNat updated))
      else .error .revert
  | SVal.map entries dflt, Seg.at i :: rest, new =>
      match lookupBy i entries with
      | some old => do
          let updated ← old.save rest new
          .ok (SVal.map (setBy i updated entries) dflt)
      | none => do
          let updated ← dflt.save rest new
          .ok (SVal.map (setBy i updated entries) dflt)
  -- The same four mismatches as `find`, with one asymmetry: there is no
  -- `Seg.field "length"` arm, because assigning `a.length` has been a
  -- solc compile error since 0.6.
  | SVal.prim _, _ :: _, _ => .error .stuck
  | SVal.struct _, Seg.at _ :: _, _ => .error .stuck
  | SVal.array _, Seg.field _ :: _, _ => .error .stuck
  | SVal.map _ _, Seg.field _ :: _, _ => .error .stuck

namespace State

def findStorage (s : State) (root : Name) (segs : List Seg) : Res SVal :=
  match lookupBy root s.storage with
  | some v => v.find segs
  | none => .error .stuck

def saveStorage (s : State) (root : Name) (segs : List Seg) (new : SVal) :
    Res State :=
  match lookupBy root s.storage with
  | some v => do
      let updated ← v.save segs new
      .ok { s with storage := setBy root updated s.storage }
  | none => .error .stuck

def getEnv (s : State) (name : Name) : Res Binding :=
  match lookupBy name s.env with
  | some b => .ok b
  | none => .error .stuck

def setEnv (s : State) (name : Name) (b : Binding) : State :=
  { s with env := setBy name b s.env }

def getObj (s : State) (id : Nat) : Res MObj :=
  match lookupBy id s.heap with
  | some obj => .ok obj
  | none => .error .stuck

def setObj (s : State) (id : Nat) (obj : MObj) : State :=
  { s with heap := setBy id obj s.heap }

def alloc (s : State) (obj : MObj) : State × Nat :=
  ({ s with heap := setBy s.nextId obj s.heap, nextId := s.nextId + 1 },
    s.nextId)

def getNet (s : State) (addr : Int) : Int :=
  (lookupBy addr s.net).getD 0

def setNet (s : State) (addr amount : Int) : State :=
  { s with net := setBy addr amount s.net }

end State

/-! ## Cross-domain copies (`copySt` / `copyMem`) -/

mutual
/-- Deep-copy a storage value into fresh memory objects
(`copySt`: storage → memory). Mappings are not allowed in memory. -/
def copyStToM (s : State) : SVal -> Res (State × MVal)
  | SVal.int v => .ok (s, MVal.int v)
  | SVal.bool b => .ok (s, MVal.bool b)
  | SVal.struct fields => do
      let (s, mfields) ← copyStFields s fields
      let (s, id) := s.alloc (MObj.struct mfields)
      .ok (s, MVal.ref id)
  | SVal.array elems => do
      let (s, melems) ← copyStElems s elems
      let (s, id) := s.alloc (MObj.array melems)
      .ok (s, MVal.ref id)
  | SVal.map _ _ => .error .stuck

def copyStFields (s : State) :
    List (Name × SVal) -> Res (State × List (Name × MVal))
  | [] => .ok (s, [])
  | (name, v) :: rest => do
      let (s, mv) ← copyStToM s v
      let (s, mrest) ← copyStFields s rest
      .ok (s, (name, mv) :: mrest)

def copyStElems (s : State) : List SVal -> Res (State × List MVal)
  | [] => .ok (s, [])
  | v :: rest => do
      let (s, mv) ← copyStToM s v
      let (s, mrest) ← copyStElems s rest
      .ok (s, mv :: mrest)
end

/-- Fresh default memory allocation for a declared type
(`memoryReferenceDeclFreshAlloc` / `memoryArrayDeclFreshAlloc`). -/
def allocDefault (s : State) (ref : RefTy) : Res (State × Nat) :=
  match copyStToM s (defaultForRef ref) with
  | .ok (s, MVal.ref id) => .ok (s, id)
  -- A primitive default has no identity to bind.  The `.error` arm maps
  -- a propagated halt to `.stuck`, which is what the wildcard did and is
  -- currently exact: `copyStToM`'s only failure is `.stuck` (its mapping
  -- arm).  Propagating `e` instead would need that as a theorem.
  | .ok (_, MVal.prim _) => .error .stuck
  | .error _ => .error .stuck

-- `hmem` is used only by `decreasing_by`, which the linter does not see.
set_option linter.unusedVariables false in
mutual
/-- Deep-copy a memory value into a storage value
(`copyMem`: memory → storage).

`rem` is the set of heap identities still unvisited **on this path**:
following a reference consumes its identity, so a cycle runs out of
identities and is stuck, while sharing across siblings (a DAG) is
unaffected — `copyMFields`/`copyMElems` hand each child the same `rem`.
This replaces the old fuel counter, whose exhaustion arm was a case the
type did not force anyone to think about; the recursion now terminates on
`rem.length` and Lean checks it. -/
def copyMToSt (s : State) (rem : List Nat) : MVal -> Res SVal
  | MVal.int v => .ok (SVal.int v)
  | MVal.bool b => .ok (SVal.bool b)
  | MVal.ref id =>
      if hmem : id ∈ rem then
        match s.getObj id with
        | .ok (MObj.struct fields) => do
            let sfields ← copyMFields s (rem.erase id) fields
            .ok (SVal.struct sfields)
        | .ok (MObj.array elems) => do
            let selems ← copyMElems s (rem.erase id) elems
            .ok (SVal.array selems)
        | .error e => .error e
      else .error .stuck
termination_by (rem.length, 0)
decreasing_by all_goals
  (apply Prod.Lex.left
   have h1 := List.length_erase_of_mem hmem
   have h2 := List.length_pos_of_mem hmem
   omega)

def copyMFields (s : State) (rem : List Nat) :
    List (Name × MVal) -> Res (List (Name × SVal))
  | [] => .ok []
  | (name, v) :: rest => do
      let sv ← copyMToSt s rem v
      let srest ← copyMFields s rem rest
      .ok ((name, sv) :: srest)
termination_by fields => (rem.length, fields.length + 1)
decreasing_by all_goals (apply Prod.Lex.right; simp <;> omega)

def copyMElems (s : State) (rem : List Nat) : List MVal -> Res (List SVal)
  | [] => .ok []
  | v :: rest => do
      let sv ← copyMToSt s rem v
      let srest ← copyMElems s rem rest
      .ok (sv :: srest)
termination_by elems => (rem.length, elems.length + 1)
decreasing_by all_goals (apply Prod.Lex.right; simp <;> omega)
end

def copyMem (s : State) (v : MVal) : Res SVal :=
  copyMToSt s (s.heap.map Prod.fst) v

/-! ## Operator semantics -/

def Value.asInt : Value -> Res Int
  | Value.int v => .ok v
  | Value.bool _ => .error .stuck

def Value.asBool : Value -> Res Bool
  | Value.bool b => .ok b
  | Value.int _ => .error .stuck

def SVal.asValue : SVal -> Res Value
  | SVal.int v => .ok (Value.int v)
  | SVal.bool b => .ok (Value.bool b)
  | SVal.struct _ => .error .stuck
  | SVal.array _ => .error .stuck
  | SVal.map _ _ => .error .stuck

def MVal.asValue : MVal -> Res Value
  | MVal.int v => .ok (Value.int v)
  | MVal.bool b => .ok (Value.bool b)
  | MVal.ref _ => .error .stuck

def Value.toSVal : Value -> SVal
  | Value.int v => SVal.int v
  | Value.bool b => SVal.bool b

def Value.toMVal : Value -> MVal
  | Value.int v => MVal.int v
  | Value.bool b => MVal.bool b

/-- Arithmetic and relational operators on values. `/` and `%` revert on
a zero divisor (KeY `divisionAssignment`/`moduloAssignment`); `**` with a
negative exponent is stuck. -/
def applyBinOp (op : BinOp) (l r : Value) : Res Value :=
  match op with
  | .add => do .ok (Value.int ((← l.asInt) + (← r.asInt)))
  | .sub => do .ok (Value.int ((← l.asInt) - (← r.asInt)))
  | .mul => do .ok (Value.int ((← l.asInt) * (← r.asInt)))
  | .pow => do
      let b ← l.asInt
      let e ← r.asInt
      if e < 0 then .error .stuck else .ok (Value.int (b ^ e.toNat))
  | .div => do
      let d ← r.asInt
      if d = 0 then .error .revert
      else .ok (Value.int (Int.tdiv (← l.asInt) d))
  | .mod => do
      let d ← r.asInt
      if d = 0 then .error .revert
      else .ok (Value.int (Int.tmod (← l.asInt) d))
  | .lt => do .ok (Value.bool (decide ((← l.asInt) < (← r.asInt))))
  | .gt => do .ok (Value.bool (decide ((← r.asInt) < (← l.asInt))))
  | .le => do .ok (Value.bool (decide ((← l.asInt) ≤ (← r.asInt))))
  | .ge => do .ok (Value.bool (decide ((← r.asInt) ≤ (← l.asInt))))
  | .eqB => .ok (Value.bool (decide (l = r)))
  | .neB => .ok (Value.bool (!decide (l = r)))
  | .and => do .ok (Value.bool ((← l.asBool) && (← r.asBool)))
  | .or => do .ok (Value.bool ((← l.asBool) || (← r.asBool)))

def applyUnOp (op : UnOp) (v : Value) : Res Value :=
  match op with
  | .neg => do .ok (Value.int (-(← v.asInt)))
  | .not => do .ok (Value.bool (!(← v.asBool)))

/-! ## Checked arithmetic (solc ≥ 0.8)

`uint` is `uint256` and `int` is `int256`. Since Solidity 0.8,
arithmetic is checked by default: a result outside its type's range
reverts (`Panic(0x11)`). The gate is type-directed — comparisons and
boolean connectives produce `bool` and pass through untouched — and it
runs on the *result* type of the operation, which for arithmetic is the
operand type (`BinOp.retTy`). Unary minus is checked only at `Ty.int`:
solc rejects `-x` on an unsigned operand at compile time, so there is
no run-time behavior to mirror, and the parser types bare numeric
literals (including the `-5` of spec postconditions) as `uint`. -/

/-- `2^256`, the exclusive upper bound of `uint256` (cast from `Nat`,
where kernel arithmetic on the literal is fast). -/
def uintBound : Int := ((2 ^ 256 : Nat) : Int)

/-- `2^255`, the exclusive upper bound (and negated inclusive lower
bound) of `int256`. -/
def intBound : Int := ((2 ^ 255 : Nat) : Int)

/-- Checked-arithmetic gate: revert when an arithmetic result leaves
its Solidity type's range (solc's `Panic(0x11)`); non-integer results
and non-arithmetic types pass through. -/
def checkArith (ty : Ty) : Value -> Res Value
  | Value.int n =>
      match ty with
      | Ty.uint =>
          if 0 ≤ n ∧ n < uintBound then .ok (Value.int n)
          else .error .revert
      | Ty.int =>
          if -intBound ≤ n ∧ n < intBound then .ok (Value.int n)
          else .error .revert
      -- An integer at a non-arithmetic type skips the range gate.  Only
      -- reachable through kind confusion, which `wtExpr` does not pin.
      | Ty.bool => .ok (Value.int n)
      | Ty.ref _ => .ok (Value.int n)
  | Value.bool b => .ok (Value.bool b)

/-- `checkArith` is a guard: on success it returns its input. -/
theorem checkArith_ok_eq {ty : Ty} {v w : Value}
    (h : checkArith ty v = .ok w) : w = v := by
  cases v with
  | bool b => exact (Except.ok.inj h).symm
  | int n =>
      cases ty with
      | prim p =>
          cases p with
          | uint =>
              simp only [checkArith] at h
              by_cases hb : 0 ≤ n ∧ n < uintBound
              · rw [if_pos hb] at h
                exact (Except.ok.inj h).symm
              · rw [if_neg hb] at h
                exact nomatch h
          | int =>
              simp only [checkArith] at h
              by_cases hb : -intBound ≤ n ∧ n < intBound
              · rw [if_pos hb] at h
                exact (Except.ok.inj h).symm
              · rw [if_neg hb] at h
                exact nomatch h
          | bool => exact (Except.ok.inj h).symm
      | ref r => exact (Except.ok.inj h).symm

/-! ## Places, expression evaluation, statement execution

Expression evaluation threads the state because `++`/`--` mutate it.
Sub-expressions evaluate left to right; `&&`/`||` short-circuit.

The mutual block below terminates on the measure `4 * e.size + rank`:
every cross-call either recurses into a strict sub-expression
(`WrappedExpr.size` drops, and it never drops by less than the rank span
of `4`) or stays on a size-equal expression while moving to a
lower-ranked function (`resolveS`/`resolveMBase` = 0, `readM`/`resolveLoc`
= 1, `evalValue`/`writeValue` = 2, `evalInt` = 3). `WrappedExpr.size`
ignores the type argument, so `resolveLoc` re-wrapping a field expression
with `Ty.uint` is size-neutral. -/

/-- A resolved assignment target. -/
inductive Loc where
  | stack (name : Name)
  | storageLocal (name : Name)
  | memoryRoot (name : Name)
  | storage (root : Name) (segs : List Seg)
  | memoryField (id : Nat) (field : Name)
  | memoryIndex (id : Nat) (i : Int)

/-- Read the primitive value held at a resolved location. Resolution
already ran, so this is side-effect free: it is what lets `++`/`--` and
`op=` evaluate their l-value exactly once, the way solc compiles them.
Alias roots (`storageLocal`, `memoryRoot`) bind references, not
primitives, and are stuck. -/
def readLoc (s : State) : Loc -> Res Value
  | Loc.stack name => do
      match ← s.getEnv name with
      | Binding.val v => .ok v
      | Binding.spath _ _ => .error .stuck
      | Binding.mref _ => .error .stuck
  | Loc.storageLocal _ => .error .stuck
  | Loc.memoryRoot _ => .error .stuck
  | Loc.storage root segs => do
      (← s.findStorage root segs).asValue
  | Loc.memoryField id fld => do
      match ← s.getObj id with
      | MObj.struct fields =>
          match lookupBy fld fields with
          | some v => v.asValue
          | none => .error .stuck
      | MObj.array _ => .error .stuck
  | Loc.memoryIndex id i => do
      match ← s.getObj id with
      | MObj.array elems =>
          if h : 0 ≤ i ∧ i.toNat < elems.length then
            (elems.get ⟨i.toNat, h.2⟩).asValue
          else .error .revert
      | MObj.struct _ => .error .stuck

/-- Write a primitive value at a resolved location: the write half of
`writeValue`, after resolution. Alias roots are stuck, as in
`writeValue`. -/
def writeLoc (s : State) (loc : Loc) (v : Value) : Res State :=
  match loc with
  | Loc.stack name => .ok (s.setEnv name (Binding.val v))
  | Loc.storage root segs => s.saveStorage root segs v.toSVal
  | Loc.memoryField id fld => do
      match ← s.getObj id with
      | MObj.struct fields =>
          .ok (s.setObj id (MObj.struct (setBy fld v.toMVal fields)))
      | MObj.array _ => .error .stuck
  | Loc.memoryIndex id i => do
      match ← s.getObj id with
      | MObj.array elems =>
          if 0 ≤ i ∧ i.toNat < elems.length then
            .ok (s.setObj id (MObj.array (elems.set i.toNat v.toMVal)))
          else .error .revert
      | MObj.struct _ => .error .stuck
  | Loc.storageLocal _ => .error .stuck
  | Loc.memoryRoot _ => .error .stuck

mutual

/-- Resolve a storage-kind place expression to a root and path,
evaluating (and possibly mutating through) embedded index
expressions. Push-lvalues extend the array with a default element and
address it. -/
def resolveS (s : State) : WrappedExpr -> Res (State × Name × List Seg)
  | WrappedExpr.var _ _ fld =>
      match lookupBy fld.name s.env with
      | some (Binding.spath root segs) => .ok (s, root, segs)
      | some (Binding.val _) => .error .stuck
      | some (Binding.mref _) => .error .stuck
      | none =>
          if fld.origin = some StorageOrigin.global then
            .ok (s, fld.name, [])
          else .error .stuck
  | WrappedExpr.field _ _ base fld => do
      let (s, root, segs) ← resolveS s base
      .ok (s, root, segs ++ [Seg.field fld.name])
  | WrappedExpr.index _ _ base index => do
      let (s, root, segs) ← resolveS s base
      let (s, i) ← evalInt s index
      .ok (s, root, segs ++ [Seg.at i])
  | WrappedExpr.pushPlace target => do
      let (s, root, segs) ← resolveS s target
      let arr ← s.findStorage root segs
      match arr, target.ty with
      | SVal.array elems, Ty.ref (RefTy.array elemTy) => do
          let extended := SVal.array (elems ++ [defaultForTy elemTy])
          let s ← s.saveStorage root segs extended
          .ok (s, root, segs ++ [Seg.at elems.length])
      -- The two mismatches kept apart rather than answered by one joint
      -- wildcard: a node that is not an array, and a target whose type is
      -- not an array reference.
      | SVal.prim _, _ => .error .stuck
      | SVal.struct _, _ => .error .stuck
      | SVal.map _ _, _ => .error .stuck
      | SVal.array _, Ty.prim _ => .error .stuck
      | SVal.array _, Ty.ref (RefTy.struct _) => .error .stuck
      | SVal.array _, Ty.ref (RefTy.mapping _ _) => .error .stuck
  -- The seven constructors that are not places. Listed rather than left
  -- to a wildcard, so a new `WrappedExpr` constructor is a compile error
  -- here instead of silently becoming stuck; the same seven arms close
  -- `resolveMBase`, `readM` and `resolveLoc` below.
  | WrappedExpr.bool _ => .error .stuck
  | WrappedExpr.intLit _ _ => .error .stuck
  | .mkCall _ _ _ _ => .error .stuck
  | .mkBinop _ _ _ => .error .stuck
  | .mkUnop _ _ => .error .stuck
  | .mkIncDec _ _ => .error .stuck
  | .mkTernary _ _ _ => .error .stuck
termination_by e => 4 * e.size + 0
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

/-- Resolve a memory place expression down to its base object identity,
following references field by field. Returns the identity holding the
final selector. -/
def resolveMBase (s : State) : WrappedExpr -> Res (State × Nat)
  | WrappedExpr.var _ _ fld => do
      match ← s.getEnv fld.name with
      | Binding.mref id => .ok (s, id)
      | Binding.val _ => .error .stuck
      | Binding.spath _ _ => .error .stuck
  | WrappedExpr.field _ _ base fld => do
      let (s, baseId) ← resolveMBase s base
      match ← s.getObj baseId with
      | MObj.struct fields =>
          match lookupBy fld.name fields with
          | some (MVal.ref id) => .ok (s, id)
          | some (MVal.prim _) => .error .stuck
          | none => .error .stuck
      | MObj.array _ => .error .stuck
  | WrappedExpr.index _ _ base index => do
      let (s, baseId) ← resolveMBase s base
      let (s, i) ← evalInt s index
      match ← s.getObj baseId with
      | MObj.array elems =>
          if h : 0 ≤ i ∧ i.toNat < elems.length then
            match elems.get ⟨i.toNat, h.2⟩ with
            | MVal.ref id => .ok (s, id)
            | MVal.prim _ => .error .stuck
          else .error .revert
      | MObj.struct _ => .error .stuck
  | WrappedExpr.pushPlace _ => .error .stuck
  | WrappedExpr.bool _ => .error .stuck
  | WrappedExpr.intLit _ _ => .error .stuck
  | .mkCall _ _ _ _ => .error .stuck
  | .mkBinop _ _ _ => .error .stuck
  | .mkUnop _ _ => .error .stuck
  | .mkIncDec _ _ => .error .stuck
  | .mkTernary _ _ _ => .error .stuck
termination_by e => 4 * e.size + 0
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

/-- Read the memory slot addressed by a place expression. -/
def readM (s : State) : WrappedExpr -> Res (State × MVal)
  | WrappedExpr.var _ _ fld => do
      match ← s.getEnv fld.name with
      | Binding.mref id => .ok (s, MVal.ref id)
      | Binding.val _ => .error .stuck
      | Binding.spath _ _ => .error .stuck
  | WrappedExpr.field _ _ base fld => do
      let (s, baseId) ← resolveMBase s base
      match ← s.getObj baseId with
      | MObj.struct fields =>
          match lookupBy fld.name fields with
          | some v => .ok (s, v)
          | none => .error .stuck
      | MObj.array _ => .error .stuck
  | WrappedExpr.index _ _ base index => do
      let (s, baseId) ← resolveMBase s base
      let (s, i) ← evalInt s index
      match ← s.getObj baseId with
      | MObj.array elems =>
          if h : 0 ≤ i ∧ i.toNat < elems.length then
            .ok (s, elems.get ⟨i.toNat, h.2⟩)
          else .error .revert
      | MObj.struct _ => .error .stuck
  | WrappedExpr.pushPlace _ => .error .stuck
  | WrappedExpr.bool _ => .error .stuck
  | WrappedExpr.intLit _ _ => .error .stuck
  | .mkCall _ _ _ _ => .error .stuck
  | .mkBinop _ _ _ => .error .stuck
  | .mkUnop _ _ => .error .stuck
  | .mkIncDec _ _ => .error .stuck
  | .mkTernary _ _ _ => .error .stuck
termination_by e => 4 * e.size + 1
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

/-- Resolve an assignable expression to an assignment target. -/
def resolveLoc (s : State) : WrappedExpr -> Res (State × Loc)
  | WrappedExpr.var kind _ fld =>
      match kind with
      | Kind.stack => .ok (s, Loc.stack fld.name)
      | Kind.memory => .ok (s, Loc.memoryRoot fld.name)
      | Kind.storage =>
          if fld.origin = some StorageOrigin.global then
            .ok (s, Loc.storage fld.name [])
          else .ok (s, Loc.storageLocal fld.name)
  | WrappedExpr.field kind _ base fld =>
      match kind with
      | Kind.storage => do
          let (s, root, segs) ←
            resolveS s (WrappedExpr.field kind (Ty.uint) base fld)
          .ok (s, Loc.storage root segs)
      | Kind.memory => do
          let (s, baseId) ← resolveMBase s base
          .ok (s, Loc.memoryField baseId fld.name)
      | Kind.stack => .error .stuck
  | WrappedExpr.index kind _ base index =>
      match kind with
      | Kind.storage => do
          let (s, root, segs) ← resolveS s base
          let (s, i) ← evalInt s index
          .ok (s, Loc.storage root (segs ++ [Seg.at i]))
      | Kind.memory => do
          let (s, baseId) ← resolveMBase s base
          let (s, i) ← evalInt s index
          .ok (s, Loc.memoryIndex baseId i)
      | Kind.stack => .error .stuck
  | WrappedExpr.pushPlace target => do
      let (s, root, segs) ← resolveS s (WrappedExpr.pushPlace target)
      .ok (s, Loc.storage root segs)
  | WrappedExpr.bool _ => .error .stuck
  | WrappedExpr.intLit _ _ => .error .stuck
  | .mkCall _ _ _ _ => .error .stuck
  | .mkBinop _ _ _ => .error .stuck
  | .mkUnop _ _ => .error .stuck
  | .mkIncDec _ _ => .error .stuck
  | .mkTernary _ _ _ => .error .stuck
termination_by e => 4 * e.size + 1
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

/-- Evaluate an expression to a primitive value. -/
def evalValue (s : State) : WrappedExpr -> Res (State × Value)
  | WrappedExpr.bool b => .ok (s, Value.bool b)
  | WrappedExpr.intLit _ v => .ok (s, Value.int v)
  | e@(WrappedExpr.var kind _ fld) =>
      match kind with
      | Kind.stack => do
          match ← s.getEnv fld.name with
          | Binding.val v => .ok (s, v)
          | Binding.spath _ _ => .error .stuck
          | Binding.mref _ => .error .stuck
      | Kind.storage => do
          let (s, root, segs) ← resolveS s e
          let v ← s.findStorage root segs
          .ok (s, ← v.asValue)
      | Kind.memory => .error .stuck
  | e@(WrappedExpr.field kind _ _ _) =>
      match kind with
      | Kind.storage => do
          let (s, root, segs) ← resolveS s e
          let v ← s.findStorage root segs
          .ok (s, ← v.asValue)
      | Kind.memory => do
          let (s, v) ← readM s e
          .ok (s, ← v.asValue)
      | Kind.stack => .error .stuck
  | e@(WrappedExpr.index kind _ _ _) =>
      match kind with
      | Kind.storage => do
          let (s, root, segs) ← resolveS s e
          let v ← s.findStorage root segs
          .ok (s, ← v.asValue)
      | Kind.memory => do
          let (s, v) ← readM s e
          .ok (s, ← v.asValue)
      | Kind.stack => .error .stuck
  | .mkBinop op l r => do
      let (s, lv) ← evalValue s l
      match op, lv with
      | BinOp.and, Value.bool false => .ok (s, Value.bool false)
      | BinOp.or, Value.bool true => .ok (s, Value.bool true)
      | _, _ => do
          let (s, rv) ← evalValue s r
          let v ← applyBinOp op lv rv
          -- Checked arithmetic at the operation's result type
          -- (`BinOp.retTy`: the operand type for arithmetic, `bool` —
          -- unconstrained — for comparisons and connectives).
          .ok (s, ← checkArith (op.retTy l.ty) v)
  | .mkUnop op arg => do
      let (s, v) ← evalValue s arg
      let v ← applyUnOp op v
      -- `-x` is checked only at `int` (`-(-2^255)` overflows); solc
      -- rejects unary minus on unsigned operands at compile time.
      match op, arg.ty with
      | UnOp.neg, Ty.int => .ok (s, ← checkArith Ty.int v)
      | _, _ => .ok (s, v)
  | .mkIncDec op target => do
      -- The l-value is resolved exactly once (solc evaluates `x++`'s
      -- target once); the old double resolution re-ran the target's
      -- index side effects on the write-back.
      let (s, loc) ← resolveLoc s target
      let old ← readLoc s loc
      let oldInt ← old.asInt
      let newInt := if op.isIncrement then oldInt + 1 else oldInt - 1
      -- Checked arithmetic: `++` past the type's maximum and `--`
      -- below its minimum revert.
      let newVal ← checkArith target.ty (Value.int newInt)
      let s ← writeLoc s loc newVal
      .ok (s, if op.isPre then newVal else old)
  -- `c ? t : e` short-circuits like `&&`/`||`: only the taken branch is
  -- evaluated (KeY's `ternaryToIf` residual has the same meaning).
  | .mkTernary c t e => do
      let (s, cv) ← evalValue s c
      match cv with
      | Value.bool true => evalValue s t
      | Value.bool false => evalValue s e
      | Value.int _ => .error .stuck
  -- `net` is picked out by name and arity, which no constructor pattern
  -- can express, so this one arm stays order-dependent: every other call
  -- falls to the `mkCall` arm below, where meaning comes from inlining
  -- (`SoliditySyntax.inlineBlock`) rather than from the interpreter.
  | .mkCall _ _ "net" [addr] => do
      let (s, a) ← evalInt s addr
      .ok (s, Value.int (s.getNet a))
  | .mkCall _ _ _ _ => .error .stuck
  | WrappedExpr.pushPlace _ => .error .stuck
termination_by e => 4 * e.size + 2
decreasing_by all_goals
  subst_vars
  first
  | omega
  | (simp [Typed.WrappedExpr.size, Typed.WrappedExpr.sizeList] <;> omega)

def evalInt (s : State) (e : WrappedExpr) : Res (State × Int) := do
  let (s, v) ← evalValue s e
  .ok (s, ← v.asInt)
termination_by 4 * e.size + 3
decreasing_by all_goals omega

/-- Write a primitive value through a place expression: resolve, then
`writeLoc`. -/
def writeValue (s : State) (target : WrappedExpr) (v : Value) :
    Res State := do
  let (s, loc) ← resolveLoc s target
  writeLoc s loc v
termination_by 4 * target.size + 2
decreasing_by all_goals omega

end

/-! ## Statement execution -/

/-- Evaluate an assignment right-hand side down to the storage value a
storage-kind target stores: primitives evaluate, storage sources copy
by value (`select`), memory sources deep-copy (`copyMem`). A storage
source whose type contains a (nested) mapping is stuck — solc ≥ 0.7
rejects that assignment at compile time. -/
def rhsToSVal (s : State) (rhs : WrappedExpr) : Res (State × SVal) :=
  if rhs.ty.isPrimitive then do
    let (s, v) ← evalValue s rhs
    .ok (s, v.toSVal)
  else
    match rhs.kind with
    | Kind.storage =>
        if tyHasMapping rhs.ty then .error .stuck
        else do
          let (s, rroot, rsegs) ← resolveS s rhs
          let v ← s.findStorage rroot rsegs
          .ok (s, v)
    | Kind.memory => do
        let (s, mv) ← readM s rhs
        let sval ← copyMem s mv
        .ok (s, sval)
    -- A non-primitive right-hand side of stack kind: `WrappedExpr.kind`
    -- of a ternary is always `.stack`, so `Person memory p = flag ? a : b;`
    -- lands here. A documented scope limit, not an oversight.
    | Kind.stack => .error .stuck

/-- Evaluate an assignment right-hand side down to the slot value a
memory-kind target stores: primitives evaluate, memory sources alias,
storage sources deep-copy (`copySt`; mappings cannot reach memory, so
`copyStToM` is stuck on them already). -/
def rhsToMVal (s : State) (rhs : WrappedExpr) : Res (State × MVal) :=
  if rhs.ty.isPrimitive then do
    let (s, v) ← evalValue s rhs
    .ok (s, v.toMVal)
  else
    match rhs.kind with
    | Kind.memory => readM s rhs
    | Kind.storage => do
        let (s, rroot, rsegs) ← resolveS s rhs
        let sval ← s.findStorage rroot rsegs
        copyStToM s sval
    -- As in `rhsToSVal`: a non-primitive stack-kind source.
    | Kind.stack => .error .stuck

/-- Assign into a nested (field/index/push) target: the right-hand
side is evaluated **before** the left-hand side's location is
resolved — solc compiles the RHS of an assignment first in both the
legacy and the IR pipeline, so index side effects interleave in that
order. -/
def execAssignNested (s : State) (lhsExpr rhs : WrappedExpr) :
    Res State :=
  match lhsExpr.kind with
  | Kind.storage => do
      let (s, sv) ← rhsToSVal s rhs
      let (s, loc) ← resolveLoc s lhsExpr
      match loc with
      | Loc.storage root segs => s.saveStorage root segs sv
      | Loc.stack _ => .error .stuck
      | Loc.storageLocal _ => .error .stuck
      | Loc.memoryRoot _ => .error .stuck
      | Loc.memoryField _ _ => .error .stuck
      | Loc.memoryIndex _ _ => .error .stuck
  | Kind.memory => do
      let (s, mv) ← rhsToMVal s rhs
      let (s, loc) ← resolveLoc s lhsExpr
      match loc with
      | Loc.memoryField id fld => do
          match ← s.getObj id with
          | MObj.struct fields =>
              .ok (s.setObj id (MObj.struct (setBy fld mv fields)))
          | MObj.array _ => .error .stuck
      | Loc.memoryIndex id i => do
          match ← s.getObj id with
          | MObj.array elems =>
              if 0 ≤ i ∧ i.toNat < elems.length then
                .ok (s.setObj id (MObj.array (elems.set i.toNat mv)))
              else .error .revert
          | MObj.struct _ => .error .stuck
      | Loc.stack _ => .error .stuck
      | Loc.storage _ _ => .error .stuck
      | Loc.storageLocal _ => .error .stuck
      | Loc.memoryRoot _ => .error .stuck
  | Kind.stack => .error .stuck

/-- Assign `rhs` into an assignable place, dispatching on the place kind
and the right-hand side's data location, mirroring the write/copy rule
families. Root targets have no embedded index expressions, so only the
right-hand side computes there; nested targets go through
`execAssignNested` (RHS first, as in solc).

The final arm is a *delegation*, not a hidden stuck case: every nested
place goes to `execAssignNested`.  Scrutinizing the `PlaceExpr` instead of
its `expr` projection would bring the `assignable` proof along and let the
match compiler refute the seven non-place constructors — the discipline
`Rules.ruleEffect` gets from its condition proof — but that match is
dependent, and Lean then generates no equation lemmas for `execAssign` and
no `execStmt.eq_def`, which `RuleSoundness.lean` and
`Wp/Terminal/UpdateDecl.lean` rewrite with in some fifty places. -/
def execAssign (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) :
    Res State :=
  match lhs.expr with
  | WrappedExpr.var kind _ fld =>
      match kind with
      | Kind.stack => do
          let (s, v) ← evalValue s rhs
          .ok (s.setEnv fld.name (Binding.val v))
      | Kind.storage =>
          if fld.origin = some StorageOrigin.global then do
            -- global storage root: value copy.
            let (s, sv) ← rhsToSVal s rhs
            s.saveStorage fld.name [] sv
          else do
            -- `storageLocalRootRebind`: a local storage root re-binds
            -- its path.
            let (s, root, segs) ← resolveS s rhs
            .ok (s.setEnv fld.name (Binding.spath root segs))
      | Kind.memory =>
          match rhs.kind with
          | Kind.memory => do
              -- `memoryRootRebind`: aliasing, no copy.
              let (s, v) ← readM s rhs
              match v with
              | MVal.ref id => .ok (s.setEnv fld.name (Binding.mref id))
              | MVal.prim _ => .error .stuck
          | Kind.storage => do
              -- storage → memory deep copy (`copySt`).
              let (s, root, segs) ← resolveS s rhs
              let sval ← s.findStorage root segs
              let (s, mv) ← copyStToM s sval
              match mv with
              | MVal.ref id => .ok (s.setEnv fld.name (Binding.mref id))
              | MVal.prim _ => .error .stuck
          | Kind.stack => .error .stuck
  | lhsExpr => execAssignNested s lhsExpr rhs

mutual

def execStmt (s : State) : Stmt -> Res State
  | Stmt.expr e => do
      let (s, _) ← evalValue s e
      .ok s
  | Stmt.assign lhs rhs => execAssign s lhs rhs
  | Stmt.storageDecl _ name init =>
      match init with
      | none => .ok s
      | some rhs => do
          let (s, root, segs) ← resolveS s rhs
          .ok (s.setEnv name (Binding.spath root segs))
  | Stmt.storagePlaceAlias _ name init => do
      let (s, root, segs) ← resolveS s init
      .ok (s.setEnv name (Binding.spath root segs))
  | Stmt.memoryDecl ty name init =>
      match init with
      | none =>
          match ty with
          | Ty.ref ref => do
              let (s, id) ← allocDefault s ref
              .ok (s.setEnv name (Binding.mref id))
          -- A memory declaration binds an object identity, so a
          -- primitive declared type has nothing to allocate.
          | Ty.prim _ => .error .stuck
      | some rhs =>
          match rhs.kind with
          | Kind.memory => do
              let (s, v) ← readM s rhs
              match v with
              | MVal.ref id => .ok (s.setEnv name (Binding.mref id))
              | MVal.prim _ => .error .stuck
          | Kind.storage => do
              let (s, root, segs) ← resolveS s rhs
              let sval ← s.findStorage root segs
              let (s, mv) ← copyStToM s sval
              match mv with
              | MVal.ref id => .ok (s.setEnv name (Binding.mref id))
              | MVal.prim _ => .error .stuck
          | Kind.stack => .error .stuck
  | Stmt.stackDecl ty name init =>
      match init with
      | none =>
          match ty with
          | Ty.bool => .ok (s.setEnv name (Binding.val (Value.bool false)))
          | Ty.uint => .ok (s.setEnv name (Binding.val (Value.int 0)))
          | Ty.int => .ok (s.setEnv name (Binding.val (Value.int 0)))
          -- A reference-typed declaration binds the integer `0` rather
          -- than being stuck, which is odd on its face: a stack binding
          -- holds a primitive, and `stmtWt` requires `ty.isPrimitive`
          -- here.  It cannot simply be made stuck, though —
          -- `valueDeclSkip`'s rule condition is `init = none` with no
          -- type side condition, so `Wp`'s `valueDeclSkip_update` is
          -- stated for every `ty` against `defaultValue`, which answers
          -- `Value.int 0` here.  Tightening one means tightening both.
          | Ty.ref _ => .ok (s.setEnv name (Binding.val (Value.int 0)))
      | some rhs => do
          let (s, v) ← evalValue s rhs
          .ok (s.setEnv name (Binding.val v))
  | Stmt.delete target =>
      match target.expr.kind with
      | Kind.storage => do
          let (s, root, segs) ← resolveS s target.expr
          let current ← s.findStorage root segs
          s.saveStorage root segs current.defaultOf
      | Kind.memory =>
          -- The second arm is a delegation over every non-root place; as
          -- in `execAssign`, closing it by destructuring the `PlaceExpr`
          -- would cost `execStmt`'s equation lemmas.
          match target.expr with
          | WrappedExpr.var _ ty fld =>
              -- `memoryRootDeleteFreshRebind`: fresh default identity.
              match ty with
              | Ty.ref ref => do
                  let (s, id) ← allocDefault s ref
                  .ok (s.setEnv fld.name (Binding.mref id))
              | Ty.prim _ => .error .stuck
          | e => do
              let (s, loc) ← resolveLoc s e
              let writeM (s : State) (mv : MVal) : Res State :=
                match loc with
                | Loc.memoryField id fld => do
                    match ← s.getObj id with
                    | MObj.struct fields =>
                        .ok (s.setObj id (MObj.struct (setBy fld mv fields)))
                    | MObj.array _ => .error .stuck
                | Loc.memoryIndex id i => do
                    match ← s.getObj id with
                    | MObj.array elems =>
                        if 0 ≤ i ∧ i.toNat < elems.length then
                          .ok (s.setObj id
                            (MObj.array (elems.set i.toNat mv)))
                        else .error .revert
                    | MObj.struct _ => .error .stuck
                | Loc.stack _ => .error .stuck
                | Loc.storage _ _ => .error .stuck
                | Loc.storageLocal _ => .error .stuck
                | Loc.memoryRoot _ => .error .stuck
              match e.ty with
              | Ty.bool => writeM s (MVal.bool false)
              | Ty.uint | Ty.int => writeM s (MVal.int 0)
              | Ty.ref ref => do
                  let (s, id) ← allocDefault s ref
                  writeM s (MVal.ref id)
      | Kind.stack => .error .stuck
  | Stmt.push target value => do
      let (s, root, segs) ← resolveS s target.expr
      let arr ← s.findStorage root segs
      match arr, target.expr.ty with
      | SVal.array elems, Ty.ref (RefTy.array elemTy) => do
          -- The pushed value goes through the same right-hand-side
          -- reading as a storage assignment (`rhsToSVal`), including
          -- the solc rejection of storage sources with (nested)
          -- mapping types. A valueless `push()` extends with the
          -- default and stays legal even for mapping-carrying element
          -- types, as in solc.
          let (s, newElem) ←
            match value with
            | none => pure (s, defaultForTy elemTy)
            | some rhs => rhsToSVal s rhs
          s.saveStorage root segs (SVal.array (elems ++ [newElem]))
      -- As in `resolveS`'s push-lvalue arm: a node that is not an array,
      -- and a target whose type is not an array reference, kept apart.
      | SVal.prim _, _ => .error .stuck
      | SVal.struct _, _ => .error .stuck
      | SVal.map _ _, _ => .error .stuck
      | SVal.array _, Ty.prim _ => .error .stuck
      | SVal.array _, Ty.ref (RefTy.struct _) => .error .stuck
      | SVal.array _, Ty.ref (RefTy.mapping _ _) => .error .stuck
  | Stmt.pushAssign target value =>
      execAssign s (PlaceExpr.pushPlace target) value
  | Stmt.pushFieldAssign target fld value =>
      execAssign s
        (PlaceExpr.field Kind.storage fld.ty
          (WrappedExpr.pushPlace target) fld)
        value
  | Stmt.pop target => do
      let (s, root, segs) ← resolveS s target.expr
      let arr ← s.findStorage root segs
      match arr with
      | SVal.array elems =>
          match elems.reverse with
          | [] => .error .revert
          | _ :: restRev =>
              s.saveStorage root segs (SVal.array restRev.reverse)
      | SVal.prim _ => .error .stuck
      | SVal.struct _ => .error .stuck
      | SVal.map _ _ => .error .stuck
  | Stmt.revert _ => .error .revert
  | Stmt.compoundAssign op lhs rhs => do
      -- `a op= e`: the right-hand side first (solc compiles assignment
      -- RHS first), then the l-value is resolved exactly **once** —
      -- read and write go through the same `Loc`, so index side
      -- effects in `a` run once, as in solc. The result is checked at
      -- the target's type.
      let (s, v) ← evalValue s rhs
      let (s, loc) ← resolveLoc s lhs.expr
      let old ← readLoc s loc
      let new ← applyBinOp op old v
      let new ← checkArith lhs.expr.ty new
      writeLoc s loc new
  | Stmt.ite cond thn els => do
      let (s, c) ← evalValue s cond
      match c with
      | Value.bool true => execBlock s thn
      | Value.bool false => execBlock s els
      | Value.int _ => .error .stuck
  | Stmt.assertStmt cond => do
      let (s, c) ← evalValue s cond
      match c with
      | Value.bool true => .ok s
      | Value.bool false => .error .revert
      | Value.int _ => .error .stuck
  /- `require` executes exactly like `assert` (revert on false); the KeY
  assert/require difference (⊥ vs revert routing) lives in the sequent
  layer — see solkey `docs/require-assert.md`: diamond `c ∧ φ`, box
  `c → φ`, which falls out of `check` on the `.revert` outcome. -/
  | Stmt.requireStmt cond => do
      let (s, c) ← evalValue s cond
      match c with
      | Value.bool true => .ok s
      | Value.bool false => .error .revert
      | Value.int _ => .error .stuck
  | Stmt.transfer recipient amount => do
      let (s, addr) ← evalInt s recipient
      let (s, amt) ← evalInt s amount
      -- `a.transfer(v)` moves `v` of the contract's own funds: it
      -- reverts when the balance cannot cover the amount (the EVM's
      -- value-transfer check that solc's `transfer` inherits), then
      -- books the debit on the `net` ledger. Amounts are `uint`-typed
      -- in Solidity, so a negative amount is an untypable program.
      if amt < 0 then .error .stuck
      else if s.selfBalance < amt then .error .revert
      else
        .ok { s.setNet addr (s.getNet addr - amt) with
                selfBalance := s.selfBalance - amt }
  /- Calls are given meaning by inlining (`SolidityJudgment.checkInlined`);
  a call reaching the interpreter directly is stuck, mirroring KeY,
  where `functionBodyExpand` is the only rule for `FunctionBodyStatement`. -/
  | Stmt.callStmt _ _ _ => .error .stuck

def execBlock (s : State) : List Stmt -> Res State
  | [] => .ok s
  | stmt :: rest => do
      let s ← execStmt s stmt
      execBlock s rest

end

/-! ## Initial state and judgment validity -/

/-- The globals of `StandardExample.sol` plus the `people` array used by the
existing worked examples. The contract starts with funds
(`selfBalance`) so the ported payment examples' transfers are covered;
insufficient-balance behavior is exercised by explicitly smaller
balances (see `Examples/Taclets/NetOps.lean`). -/
def State.exampleStore : State :=
  { selfBalance := 1000000000,
    storage :=
      [ ("total", SVal.int 0),
        ("age", SVal.int 0),
        ("owner", SVal.int 0),
        ("balance", SVal.int 0),
        ("values", SVal.array []),
        ("balances", SVal.map [] (SVal.int 0)),
        ("flags", SVal.map [] (SVal.bool false)),
        ("folks", SVal.map [] (defaultForRef (RefTy.struct "Person"))),
        ("matrix", SVal.array []),
        ("persons", SVal.array []),
        ("people", SVal.array []),
        ("alice", defaultForRef (RefTy.struct "Person")),
        ("bob", defaultForRef (RefTy.struct "Person")),
        ("wallet", defaultForRef (RefTy.struct "Wallet")) ] }

/-! ### Stores of the ported solkey contracts

One store per ported contract, not one union store. The store is an
association list the interpreter scans on every read and write, so its
length is a direct multiplier on the cost of every `sol_wp` proof: the
46-entry union of these schemas made even the fifteen `ExamplesWP`
judgments time out at `whnf`. Per-contract stores are also the faithful
reading — in solkey each `.sol` file is its own contract with its own
storage.

The eight renames that keep the *parser's* single name→type table
(`SoliditySyntax.solkeyGlobalTy`) unambiguous across contracts are noted
at their entries; `scripts/solkey-port.mjs` applies them. -/

/-- `keyext.solidity.examples/TestSuite.sol`. Starts with funds like
`exampleStore`, for the suite's transfer tests. -/
def State.testSuiteStore : State :=
  { selfBalance := 1000000000,
    storage :=
      [ ("total", SVal.int 0),
        ("age", SVal.int 0),
        ("owner", SVal.int 0),
        ("balance", SVal.int 0),
        ("values", SVal.array []),
        -- `TestSuite.a : uint[]` ports to `aux`: `a` is a local `uint`
        -- in seven `SolcExpressions` functions.
        ("aux", SVal.array []),
        ("matrix", SVal.array []),
        ("balances", SVal.map [] (SVal.int 0)),
        -- `TestSuite.people : mapping(uint => Person)` ports to `folks`;
        -- `people` is already the `Person[]` of the calculus examples.
        ("folks", SVal.map [] (defaultForRef (RefTy.struct "Person"))),
        ("flags", SVal.map [] (SVal.bool false)),
        ("valuesMap", SVal.map [] (SVal.int 0)),
        ("accountMap", SVal.map [] (defaultForRef (RefTy.struct "Account"))),
        ("persons", SVal.array []),
        ("alice", defaultForRef (RefTy.struct "Person")),
        ("bob", defaultForRef (RefTy.struct "Person")),
        ("ledger", defaultForRef (RefTy.struct "Ledger")),
        ("tokens", SVal.array []),
        ("bucket", defaultForRef (RefTy.struct "TokenBucket")),
        ("ledgerUses", SVal.array []) ] }

/-- `solc/SolcExpressions.sol`. `v` ports to `counter`: `v` is a local
`uint` in twelve functions across the suites. -/
def State.solcExpressionsStore : State :=
  { storage := [("counter", SVal.int 0)] }

/-- `solc/SolcStructs.sol`, less the `Flagged`/`Depth*` family (see
`structDef`). -/
def State.solcStructsStore : State :=
  { storage :=
      [ ("data1", defaultForRef (RefTy.struct "Simple")),
        ("withArray", defaultForRef (RefTy.struct "WithArray")),
        ("triple", defaultForRef (RefTy.struct "Triple")),
        ("neighbourBefore", SVal.int 0),
        ("neighbourAfter", SVal.int 0),
        ("source", defaultForRef (RefTy.struct "Pair")),
        ("target", defaultForRef (RefTy.struct "Pair")),
        ("pairs1", SVal.array []),
        ("pairs2", SVal.array []),
        ("campaigns", SVal.map [] (defaultForRef (RefTy.struct "Simple"))) ] }

/-- `solc/SolcArrays.sol`. -/
def State.solcArraysStore : State :=
  { storage :=
      [ ("storageArray", SVal.array []),
        ("matrix", SVal.array []),
        ("structs", SVal.array []) ] }

/-- `solc/SolcMemory.sol`. `x` ports to `outerX` (`x` is the stack `uint`
root), `inner` to `innerS` (`inner` is a local storage alias in
`SolcStructs`), `data` to `inners` (`data` is a `Depth0` state variable
in `SolcStructs`). -/
def State.solcMemoryStore : State :=
  { storage :=
      [ ("outerX", defaultForRef (RefTy.struct "Outer")),
        ("innerS", defaultForRef (RefTy.struct "Inner")),
        ("inners", SVal.array []),
        ("prims", SVal.array []) ] }

/-- `solc/SolcMappings.sol`. `s` ports to `sBox` (`s` is a local
`Inner memory` in `SolcMemory`) and `m` to `sMap` (`m` is an existing
local storage-alias name). -/
def State.solcMappingsStore : State :=
  { storage :=
      [ ("sBox", defaultForRef (RefTy.struct "S")),
        ("withSub", defaultForRef (RefTy.struct "WithSub")),
        ("sMap", SVal.map [] (defaultForRef (RefTy.struct "S"))),
        ("withSubMap", SVal.map [] (defaultForRef (RefTy.struct "WithSub"))),
        ("balances", SVal.map [] (SVal.int 0)),
        ("arrayMap", SVal.map [] (SVal.array [])),
        ("rows", SVal.array []),
        ("ledger", defaultForRef (RefTy.struct "Ledger")) ] }

/-- `solc/SolcControlFlow.sol`. -/
def State.solcControlFlowStore : State :=
  { storage :=
      [ ("sx", defaultForRef (RefTy.struct "Pair")),
        ("sy", defaultForRef (RefTy.struct "Pair")),
        ("target", defaultForRef (RefTy.struct "Pair")),
        ("values", SVal.array []) ] }

end Semantics

/-- Run a judgment: execute the block from the given initial state and
check the postcondition in the final state. A `revert` makes a box
judgment hold vacuously and a diamond judgment fail; a stuck execution
validates nothing. -/
def SolidityJudgment.check (j : SolidityJudgment)
    (s0 : Semantics.State := Semantics.State.exampleStore) : Bool :=
  match Semantics.execBlock s0 j.block.stmts with
  | .ok s =>
      -- A default, not a hidden stuck case: a postcondition that does
      -- not evaluate to a boolean validates nothing, whatever went wrong.
      -- Left as a wildcard deliberately — `CallbackSemantics.lean` and
      -- the `Wp` bridge restate this body, and they restate it in
      -- this shape.
      match Semantics.evalValue s j.post with
      | .ok (_, Semantics.Value.bool b) => b
      | _ => false
  | .error .revert => j.block.modality = SolidityModality.box
  | .error .stuck => false

/-- Validity of a dynamic-logic judgment under the executable
semantics. -/
def SolidityJudgment.Holds (j : SolidityJudgment)
    (s0 : Semantics.State := Semantics.State.exampleStore) : Prop :=
  j.check s0 = true

/-- Run a judgment whose program may contain calls: inline through the
function table (`SoliditySyntax.funDef`) to the given depth, then
`check`. `check` itself is untouched — call-free judgments mean exactly
what they did. -/
def SolidityJudgment.checkInlined (j : SolidityJudgment)
    (s0 : Semantics.State := Semantics.State.exampleStore)
    (depth : Nat := 8) : Bool :=
  (SolidityJudgment.mk
    ⟨j.block.modality, SoliditySyntax.inlineBlock depth j.block.stmts⟩
    j.post).check s0

instance (j : SolidityJudgment) (s0 : Semantics.State) :
    Decidable (j.Holds s0) :=
  inferInstanceAs (Decidable (j.check s0 = true))

namespace SemanticsExamples

/-- The goal example: write a storage field, read it back. -/
example :
    (sol!{ < alice.account.balance = 10;
             result = alice.account.balance > (result == 10) }).Holds := by
  native_decide

example : (sol!{ < result = 1 + 2 > (result == 3) }).Holds := by
  native_decide

end SemanticsExamples

end Solidity
