import Solidity.Typing.Storage

/-!
# Types and the contract

The first layer of the typed kernel (`docs/kernel-port.md`, phase 1), after
mini-solkey's `Ch02_Elab`.  A kernel term is indexed by the contract it is
written against, so that a field access carries the proof that the field
exists, and a statement no rule covers cannot be written.

Two choices differ from mini-solkey, both forced by the interpreter being the
reference:

* **Struct bodies are `Semantics.structDef`.**  The interpreter expands a
  struct through that table, so a contract that declared its own bodies could
  disagree with what runs.  A contract is its storage roots; `fieldType` reads
  the table, and an unknown struct has no fields, so no field of it can be
  written.
* **A contract is a `Layout`** with the notation around it: `Contract.layout`
  is what `Semantics.stmtWt` reads, and `rootType_tyAt`/`fieldType_segTy`
  say the two agree.

Each ported contract is a named constant (the quoters of the later layers
need a constant to point at), written in `contract!{ … }`, and checked
against the interpreter's store for it by `initStorage_*`: the roots, their
order and their default values are the store's, so a typo in either is a
build error.
-/

namespace Solidity

namespace Ty

/-! ## The four shapes of a type

`Ty` is `prim | ref`, with the reference sorts one level down.  Every
case split in the kernel wants the four source-level shapes at once. -/

@[match_pattern, reducible] def struct (n : Name) : Ty := .ref (.struct n)
@[match_pattern, reducible] def array (T : Ty) : Ty := .ref (.array T)
@[match_pattern, reducible] def mapping (K V : Ty) : Ty := .ref (.mapping K V)

/-- `cases T` in the kernel gives the four shapes a Solidity type is written
in: `uint x` and `bool b` (a primitive), `Person p`, `uint[] xs`,
`mapping(uint => uint) m`. -/
@[elab_as_elim]
def casesOn4 {motive : Ty → Sort u} (prim : ∀ p, motive (.prim p))
    (struct : ∀ n, motive (.struct n)) (array : ∀ T, motive (.array T))
    (mapping : ∀ K V, motive (.mapping K V)) : ∀ T, motive T
  | .prim p => prim p
  | .ref (.struct n) => struct n
  | .ref (.array T) => array T
  | .ref (.mapping K V) => mapping K V

end Ty

namespace Kernel

open Semantics

/-! ## Mapping-free types

A storage copy of a type that holds a mapping is stuck (`rhsToSVal`) and
rejected by solc, so a kernel copy carries `T.mapFree = true`.  `tyHasMapping`
is the interpreter's check, but it is well-founded recursion through
`structDef`, which the kernel cannot evaluate, so a proof of it cannot be
`Eq.refl`.  `Ty.mapFree` is structural instead: a struct is mapping-free when
it is listed in `mapFreeStructs`, and `mapFreeStructs_ok` checks the list
against `tyHasMapping` once.  A struct left off the list is only
conservative: its copies cannot be written. -/

/-- The structs of `structDef` that hold no mapping. -/
def mapFreeStructs : List Name :=
  ["Token", "Account", "Person", "Basket", "TokenBucket", "Toggle", "Pair", "S", "Sub",
   "WithSub", "Inner", "Outer", "Simple", "WithArray", "Triple", "BadDup"]

/-- Every listed struct holds no mapping: `Person` (an `Account` and a
`uint`) does not, `Wallet` (with its `stash`) is not listed. -/
theorem mapFreeStructs_ok : ∀ s ∈ mapFreeStructs, tyHasMapping (.struct s) = false := by
  simp [mapFreeStructs, tyHasMapping, fieldsHaveMapping, structDef]

/-- `T` holds no mapping, by structural recursion (so by `Eq.refl`). -/
def _root_.Solidity.Ty.mapFree : Ty → Bool
  | .prim _ => true
  | .ref (.mapping ..) => false
  | .ref (.struct s) => s ∈ mapFreeStructs
  | .ref (.array e) => e.mapFree

/-- `mapFree` is the interpreter's check: a `Person[]` copies, a
`mapping(uint => uint)` does not. -/
theorem _root_.Solidity.Ty.mapFree_sound : ∀ {T : Ty}, T.mapFree = true → tyHasMapping T = false
  | .prim _, _ => by simp [tyHasMapping]
  | .ref (.mapping ..), h => by simp [Ty.mapFree] at h
  | .ref (.struct s), h => mapFreeStructs_ok s (by simpa [Ty.mapFree] using h)
  | .ref (.array e), h => by
      rw [tyHasMapping]; exact Ty.mapFree_sound (T := e) (by simpa [Ty.mapFree] using h)

/-! ## The contract -/

/-- A contract: its storage roots, in declaration order. -/
structure Contract where
  vars : List (Name × Ty)
  deriving Repr, Inhabited

namespace Contract

/-- The layout `Semantics.stmtWt` types a statement against. -/
def layout (C : Contract) : Layout := ⟨C.vars⟩

/-- The declared type of the storage root `r`. -/
def rootType (C : Contract) (r : Name) : Option Ty := lookupBy r C.vars

/-- The declared type of member `f` of struct `s`, from `structDef`.  The
contract does not enter: struct bodies are package-wide (see the module
docstring), and the parameter is there so kernel terms read `C.fieldType`. -/
def fieldType (_C : Contract) (s f : Name) : Option Ty := lookupBy f (structDef s)

/-- The storage a contract starts with: each root at its type's default. -/
def initStorage (C : Contract) : List (Name × SVal) :=
  C.vars.map fun (n, T) => (n, defaultForTy T)

/-- A root's declared type is its type in the layout at the empty path.
In `contract!{ Person alice; }`, `alice` has type `Person` in both. -/
theorem rootType_tyAt (C : Contract) (r : Name) :
    C.rootType r = C.layout.tyAt r [] := by
  simp only [rootType, layout, Layout.tyAt]
  cases lookupBy r C.vars <;> rfl

/-- A member's declared type is the layout's type one `.field` segment
down.  `alice.age` is `uint` because `Person`'s `age` is. -/
theorem fieldType_segTy {C : Contract} {s f : Name} {T : Ty}
    (h : C.fieldType s f = some T) : segTy (.struct s) (.field f) = some T := h

end Contract

/-- The contract a kernel term is written against when the notation does not
name one.  Instances are `local`: a file of examples picks its contract. -/
class InContract where
  contract : Contract

/-! ## `contract!{ … }` -/

declare_syntax_cat kernel_ty (behavior := both)
syntax:max ident : kernel_ty
syntax:max &"mapping" "(" kernel_ty " => " kernel_ty ")" : kernel_ty
syntax:max kernel_ty:max "[" "]" : kernel_ty

declare_syntax_cat kernel_member (behavior := both)
syntax kernel_ty ident ";" : kernel_member

/-- `contract!{ uint total; Person alice; mapping(uint => Person) folks; }`:
a contract written as Solidity declares its state. -/
syntax "contract!{" kernel_member* "}" : term

/-- `sol_ty!(mapping(uint => Person))`: a type written as Solidity does. -/
syntax "sol_ty!(" kernel_ty ")" : term

macro_rules
  | `(sol_ty!($x:ident)) =>
      match x.getId.toString with
      | "uint" | "address" => `(Ty.uint)
      | "int" => `(Ty.int)
      | "bool" => `(Ty.bool)
      | s => `(Ty.struct $(Lean.quote s))
  | `(sol_ty!(mapping($K => $V))) => `(Ty.mapping sol_ty!($K) sol_ty!($V))
  | `(sol_ty!($T[])) => `(Ty.array sol_ty!($T))

macro_rules
  | `(contract!{ $ms:kernel_member* }) => do
      let rows ← ms.mapM fun
        | `(kernel_member| $T:kernel_ty $x:ident ;) =>
            `(($(Lean.quote x.getId.toString), sol_ty!($T)))
        | _ => Lean.Macro.throwUnsupported
      `(({ vars := [$rows,*] } : Contract))

/-! ## The ported contracts

One per store of `Semantics.lean`, under the store's renames (noted there),
and `address` read as `uint` as the interpreter does. -/

/-- `StandardExample.sol` with the `people` array of the worked examples:
the roots of `State.exampleStore`. -/
def StandardExample : Contract := contract!{
  uint total; uint age; uint owner; uint balance;
  uint[] values;
  mapping(uint => uint) balances;
  mapping(uint => bool) flags;
  mapping(uint => Person) folks;
  uint[][] matrix;
  Person[] persons;
  Person[] people;
  Person alice; Person bob;
  Wallet wallet;
}

/-- `TestSuite.sol`, as ported (`State.testSuiteStore`). -/
def TestSuite : Contract := contract!{
  uint total; uint age; uint owner; uint balance;
  uint[] values; uint[] aux;
  uint[][] matrix;
  mapping(uint => uint) balances;
  mapping(uint => Person) folks;
  mapping(uint => bool) flags;
  mapping(uint => uint) valuesMap;
  mapping(uint => Account) accountMap;
  Person[] persons;
  Person alice; Person bob;
  Ledger ledger;
  Token[] tokens;
  TokenBucket bucket;
  LedgerUse[] ledgerUses;
  bool flag; bool flag2;
  bool[] boolFlags;
  Toggle toggle;
  Token tok;
  TokenBucket[] buckets;
  Basket basketA; Basket basketB;
}

/-- `solc/SolcExpressions.sol` (`State.solcExpressionsStore`). -/
def SolcExpressions : Contract := contract!{ uint counter; }

/-- `solc/SolcStructs.sol`, less the `Flagged`/`Depth*` family
(`State.solcStructsStore`). -/
def SolcStructs : Contract := contract!{
  Simple data1; WithArray withArray; Triple triple;
  uint neighbourBefore; uint neighbourAfter;
  Pair source; Pair target;
  Pair[] pairs1; Pair[] pairs2;
  mapping(uint => Simple) campaigns;
}

/-- `solc/SolcArrays.sol` (`State.solcArraysStore`). -/
def SolcArrays : Contract := contract!{
  uint[] storageArray; uint[][] matrix; Pair[] structs;
}

/-- `solc/SolcMemory.sol` (`State.solcMemoryStore`). -/
def SolcMemory : Contract := contract!{
  Outer outerX; Inner innerS; Inner[] inners; uint[] prims;
}

/-- `solc/SolcMappings.sol` (`State.solcMappingsStore`). -/
def SolcMappings : Contract := contract!{
  S sBox; WithSub withSub;
  mapping(uint => S) sMap;
  mapping(uint => WithSub) withSubMap;
  mapping(uint => uint) balances;
  mapping(uint => uint[]) arrayMap;
  uint[][] rows;
  Ledger ledger;
}

/-- `solc/SolcControlFlow.sol` (`State.solcControlFlowStore`). -/
def SolcControlFlow : Contract := contract!{
  Pair sx; Pair sy; Pair target; uint[] values;
}

/-! ### Each contract starts in its store -/

section
open Contract

/-- `StandardExample` declares exactly the roots `State.exampleStore` holds,
in order, each at its default: `uint total;` starts at `0`, `Person alice;`
at the default `Person`. -/
theorem initStorage_standardExample :
    StandardExample.initStorage = State.exampleStore.storage := by
  simp [StandardExample, initStorage, State.exampleStore, defaultForRef, defaultForTy]

/-- `TestSuite` starts in `State.testSuiteStore`; `bool flag;` at `false`. -/
theorem initStorage_testSuite :
    TestSuite.initStorage = State.testSuiteStore.storage := by
  simp [TestSuite, initStorage, State.testSuiteStore, defaultForRef, defaultForTy]

/-- `SolcExpressions` starts in its store: `uint counter;` at `0`. -/
theorem initStorage_solcExpressions :
    SolcExpressions.initStorage = State.solcExpressionsStore.storage := by
  simp [SolcExpressions, initStorage, State.solcExpressionsStore, defaultForTy]

/-- `SolcStructs` starts in its store: `Pair source;` at the default `Pair`. -/
theorem initStorage_solcStructs :
    SolcStructs.initStorage = State.solcStructsStore.storage := by
  simp [SolcStructs, initStorage, State.solcStructsStore, defaultForRef, defaultForTy]

/-- `SolcArrays` starts in its store: `uint[] storageArray;` empty. -/
theorem initStorage_solcArrays :
    SolcArrays.initStorage = State.solcArraysStore.storage := by
  simp [SolcArrays, initStorage, State.solcArraysStore, defaultForTy]

/-- `SolcMemory` starts in its store: `Outer outerX;` at the default `Outer`. -/
theorem initStorage_solcMemory :
    SolcMemory.initStorage = State.solcMemoryStore.storage := by
  simp [SolcMemory, initStorage, State.solcMemoryStore, defaultForRef, defaultForTy]

/-- `SolcMappings` starts in its store: `mapping(uint => S) sMap;` maps every
key to the default `S`. -/
theorem initStorage_solcMappings :
    SolcMappings.initStorage = State.solcMappingsStore.storage := by
  simp [SolcMappings, initStorage, State.solcMappingsStore, defaultForRef, defaultForTy]

/-- `SolcControlFlow` starts in its store: `uint[] values;` empty. -/
theorem initStorage_solcControlFlow :
    SolcControlFlow.initStorage = State.solcControlFlowStore.storage := by
  simp [SolcControlFlow, initStorage, State.solcControlFlowStore, defaultForRef,
    defaultForTy]

end

/-- A type in the notation is the `Ty` it names: `Person[]` is an array of
the struct `Person`. -/
example : sol_ty!(mapping(uint => Person[])) = .mapping .uint (.array (.struct "Person")) := rfl

example : StandardExample.rootType "folks" = some sol_ty!(mapping(uint => Person)) := rfl

example : StandardExample.fieldType "Person" "age" = some sol_ty!(uint) := rfl

example : sol_ty!(Person[]).mapFree = true := rfl

end Kernel
end Solidity
