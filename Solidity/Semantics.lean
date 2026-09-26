import Solidity.Syntax

/-!
# The interpreter

What a program does, the reference every rule is proved sound against
(mini-solkey's `Ch04_Semantics`).  The state is KeY's: a storage tree
(`structRules.key`), an identity-indexed memory heap (`memoryRules.key`),
the locals, and the `net` payment ledger (`netHeader.key`).  `Stmt.run`
runs a statement on it by structural recursion on the typed syntax, so
every function here terminates and every branch on a type was already
taken by the index.

Semantic conventions mirrored from KeY:
- storage assignment copies by value (`save`/`select`/`store`), memory
  assignment aliases identities, cross-domain assignments deep-copy
  (`copySt`/`copyMem`);
- array reads and writes out of bounds revert; `pop()` on an empty array
  reverts; `/` and `%` revert on a zero divisor; a failing `assert`
  reverts;
- `a.transfer(v)` books `net(a) := net(a) - v` with no callback.

Semantic conventions mirrored from solc, where KeY was more liberal
(`docs/solc-alignment.md`):
- arithmetic is **checked** (solc ≥ 0.8): a result outside its type's
  range (`uint` = `uint256`, `int` = `int256`) reverts (`checkArith`);
- an assignment evaluates its **right-hand side before resolving the
  left-hand side**, and `++`/`--` and `op=` resolve their target exactly
  once;
- `a.transfer(v)` reverts unless the contract's own funds
  (`State.selfBalance`) cover `v`, and debits them.

A run ends in a state or halts: `revert` (the program reverted) or `stuck`
(a state that does not fit the program, e.g. a local read before it is
bound).  The copy from memory back to storage terminates on the visited-set
complement `rem` (`copyMToSt`); everything else is structural.
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
  /-- A storage array: the live `elems` — `elems.length` is the array's
  length — beside the slots a `pop` has cleared and given back.  `shadow k` is
  the content of slot `elems.length + k`, so the stack is LIFO exactly as the
  slots are recycled.  This is KeY's `save(delAt(storage, at(n)), size, n±1)`
  (`storagePopSave`, `storagePushLengthSave`) read eagerly: `delete` never
  clears a mapping member, so a mapping nested in a popped element survives
  and the next `push` sees it again — solc's own behaviour, and the reason
  `pop` cannot just drop the element. -/
  | array (elems : List SVal) (shadow : List SVal)
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
  env : List (Var × Binding) := []
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

/-- Bind inversion on a successful computation. -/
theorem bind_ok_inv {x : Res α} {f : α -> Res β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

/-! The struct schema, its rank certificate and `tyHasMapping` live in
`AST.lean`: they are static-type facts (`StorageReferenceTypes.containsMapping`),
and the typed AST needs them to refuse a mapping-carrying storage copy. -/

mutual
/-- Default storage value of a type (`delete`, fresh array elements,
mapping defaults). -/
def defaultForTy : Ty -> SVal
  | Ty.bool => SVal.bool false
  | Ty.uint => SVal.int 0
  | Ty.int => SVal.int 0
  | Ty.ref (RefTy.struct name) => SVal.struct (defaultForFields (structDef name))
  | Ty.ref (RefTy.array _) => SVal.array [] []
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


/-- Shape-preserving default (`defaultOf` on the current value):
`delete` resets primitives, empties arrays, and recurses into struct
fields — but leaves mappings untouched (entries and default), the
Solidity `delete` semantics solkey implements with the lazy `delNode`
marker (`selectStDelNodeMap` reads mapping members through to the
original). A direct `delete` on a mapping is a solc compile error, so
the no-op `map` arm is unreachable from real programs.

An array is emptied outright — recycled slots and all. On the EVM the
mapping entries nested in a deleted element survive at their hashed
slots, so `delete arr; arr.push();` would see them again; KeY says
otherwise (`selectStDelNodeIndexStruct` reads every index of a deleted
node as `mtSt`) and the model follows KeY here. Matching solc would mean
`array [] (defaultOfElems elems ++ shadow)`, which takes the value out of
`Reachability.SVal.canonical` and so costs row C6 of
`WellFormedConsumers` its proof; `docs/solc-alignment.md` records the
divergence. `pop`/`push` are *not* affected — there the slot is recycled
(`pushSlot`), which is the mapping-preserving behaviour solc and KeY
agree on. -/
def SVal.defaultOf : SVal -> SVal
  | SVal.int _ => SVal.int 0
  | SVal.bool _ => SVal.bool false
  | SVal.struct fields => SVal.struct (defaultOfFields fields)
  | SVal.array _ _ => SVal.array [] []
  | SVal.map entries dflt => SVal.map entries dflt
where
  defaultOfFields : List (Name × SVal) -> List (Name × SVal)
  | [] => []
  | (name, v) :: rest => (name, v.defaultOf) :: defaultOfFields rest
/-- The slot `arr.push()` lands on, and the recycled slots that are left:
the one a `pop` cleared and handed back, or a fresh default where the array
has never been that long. KeY writes `delAt(storage, at(n))` in both cases
(`storagePushLengthSave`), which is the clear this performs — `defaultOf` is
idempotent, so clearing an already-cleared slot again is exactly that write,
and a mapping member of a recycled struct slot survives it.

`push(se)` and `push(sp)` overwrite the slot instead (KeY's
`storagePushValueSave` / `…CopySource` write a plain `save`, whose leaf would
keep the slot's mapping members). They still *consume* the slot, since it
becomes live again. The leaf is invisible there: a pushed value has the
element's type, and `rhsToSVal` is stuck on a storage source of a
mapping-carrying type while a stack source forces a primitive element, so no
push-with-value in the admitted fragment lands on a slot with a mapping.

The `isPrimitive` branch is **redundant on any well-typed storage**, where a
cleared primitive slot *is* the type's default (`pushSlot_prim`, proved in
`Typing/StoragePreservation.lean`); it is written out so that a consumer holding a
value *representation* but no typing — `Evm/Correctness.lean`, whose fragment
is primitive-element arrays — sees the pushed value without a typing
hypothesis. -/
def pushSlot (elemTy : Ty) : List SVal -> SVal × List SVal
  | [] => (defaultForTy elemTy, [])
  | c :: rest =>
      (if elemTy.isPrimitive then defaultForTy elemTy else c.defaultOf, rest)

/-- At a primitive element type the slot a `push` lands on is the type's
default, recycled or not — what `Evm/Correctness.lean` reads off it. -/
theorem pushSlot_isPrim {elemTy : Ty} {shadow : List SVal}
    (hp : elemTy.isPrimitive = true) :
    (pushSlot elemTy shadow).1 = defaultForTy elemTy := by
  cases shadow <;> simp [pushSlot, hp]

/-! ## Storage find / save -/

def SVal.find : SVal -> List Seg -> Res SVal
  | v, [] => .ok v
  | SVal.struct fields, Seg.field name :: rest =>
      match lookupBy name fields with
      | some v => v.find rest
      | none => .error .stuck
  | SVal.array elems _, Seg.at i :: rest =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then
        (elems.get ⟨i.toNat, h.2⟩).find rest
      else .error .revert
  -- `a.length`: solkey's suites assert array lengths directly
  -- (`assert(values.length == 3)`), and the parser gives `.length` a
  -- `Seg.field`, so it has to be answered here rather than by the struct
  -- arm above — an array is not a struct with a `length` member.
  | SVal.array elems _, Seg.field "length" :: rest =>
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
  | SVal.array _ _, Seg.field _ :: _ => .error .stuck
  | SVal.map _ _, Seg.field _ :: _ => .error .stuck

def SVal.save : SVal -> List Seg -> SVal -> Res SVal
  | _, [], new => .ok new
  | SVal.struct fields, Seg.field name :: rest, new =>
      match lookupBy name fields with
      | some old => do
          let updated ← old.save rest new
          .ok (SVal.struct (setBy name updated fields))
      | none => .error .stuck
  | SVal.array elems shadow, Seg.at i :: rest, new =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then do
        let updated ← (elems.get ⟨i.toNat, h.2⟩).save rest new
        .ok (SVal.array (elems.set i.toNat updated) shadow)
      else .error .revert
  | SVal.map entries dflt, Seg.at i :: rest, new =>
      match lookupBy i entries with
      | some old => do
          let updated ← old.save rest new
          .ok (SVal.map (setBy i updated entries) dflt)
      | none => do
          let updated ← dflt.save rest new
          .ok (SVal.map (setBy i updated entries) dflt)
  -- `a.length = n` is not a program assignment -- solc has rejected that
  -- since 0.6 -- but it is the calculus's own write: `push` and `pop` are
  -- `save(storage, consr(arr, size), n ± 1)` over the slot write beside it
  -- (`storagePushLengthSave`, `storagePopSave`), and this is that write read
  -- eagerly.  Growing is already done, because the `Seg.at` arm above
  -- appended; shrinking hands the cleared tail back as recycled slots, which
  -- is what makes a mapping nested in a popped element survive.
  -- The same four mismatches as `find`, with one asymmetry: there is no
  -- `Seg.field "length"` arm, because assigning `a.length` has been a
  -- solc compile error since 0.6.
  | SVal.prim _, _ :: _, _ => .error .stuck
  | SVal.struct _, Seg.at _ :: _, _ => .error .stuck
  | SVal.array _ _, Seg.field _ :: _, _ => .error .stuck
  | SVal.map _ _, Seg.field _ :: _, _ => .error .stuck

/-- `SVal.save` as the **calculus** writes it, where storage is KeY's total
map and `size` is a location like any other.

Two arms a program cannot reach, and `SVal.save` therefore does not have:
a write one past the end *appends* -- `save(storage, consr(arr, at(n)), v)`
at `n = size` is an ordinary write there, and only the companion `size` write
makes the slot visible, while here `elems` is the extent -- and a write to
`size` itself truncates, handing the cleared tail back as the recycled slots
`pushSlot` deals out.  Together they are `storagePushValueSave`,
`storagePushLengthSave` and `storagePopSave`.

A program's `a[k] = v` still reverts at `k = size` (solc, and
`Evm/BoundedSemantics.lean`), and `a.length = n` is still a compile error:
those go through `SVal.save`.  The calculus reaches this one only under an
`inBounds` guard or from a push or pop, so the two never disagree on a write
both can perform. -/
def SVal.saveExt : SVal -> List Seg -> SVal -> Res SVal
  | _, [], new => .ok new
  | SVal.struct fields, Seg.field name :: rest, new =>
      match lookupBy name fields with
      | some old => do
          let updated ← old.saveExt rest new
          .ok (SVal.struct (setBy name updated fields))
      | none => .error .stuck
  | SVal.array elems shadow, Seg.at i :: rest, new =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then do
        let updated ← (elems.get ⟨i.toNat, h.2⟩).saveExt rest new
        .ok (SVal.array (elems.set i.toNat updated) shadow)
      else if 0 ≤ i ∧ i.toNat = elems.length ∧ rest = [] then
        -- The recycled slot is consumed either way: `push(se)` overwrites the
        -- value a `pop` handed back but still takes it out of the stack,
        -- which is `pushSlot`'s second component.
        .ok (SVal.array (elems ++ [new]) (shadow.drop 1))
      else .error .revert
  | SVal.array elems shadow, Seg.field name :: rest, new =>
      if name = "length" ∧ rest = [] then
        match new with
        | SVal.int n =>
            if n = elems.length then .ok (SVal.array elems shadow)
            else if 0 ≤ n ∧ n < elems.length then
              .ok (SVal.array (elems.take n.toNat)
                ((elems.drop n.toNat).reverse.map SVal.defaultOf ++ shadow))
            else .error .revert
        | _ => .error .stuck
      else .error .stuck
  | SVal.map entries dflt, Seg.at i :: rest, new =>
      match lookupBy i entries with
      | some old => do
          let updated ← old.saveExt rest new
          .ok (SVal.map (setBy i updated entries) dflt)
      | none => do
          let updated ← dflt.saveExt rest new
          .ok (SVal.map (setBy i updated entries) dflt)
  | SVal.prim _, _ :: _, _ => .error .stuck
  | SVal.struct _, Seg.at _ :: _, _ => .error .stuck
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

/-- `saveStorage` through `SVal.saveExt`: the calculus's writer. -/
def saveStorageExt (s : State) (root : Name) (segs : List Seg) (new : SVal) :
    Res State :=
  match lookupBy root s.storage with
  | some v => do
      let updated ← v.saveExt segs new
      .ok { s with storage := setBy root updated s.storage }
  | none => .error .stuck

def getEnv (s : State) (name : Var) : Res Binding :=
  match lookupBy name s.env with
  | some b => .ok b
  | none => .error .stuck

def setEnv (s : State) (name : Var) (b : Binding) : State :=
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
  | SVal.array elems _ => do
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
            .ok (SVal.array selems [])
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
  | SVal.array _ _ => .error .stuck
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


/-! ## Memory addresses

`++`/`--` and `op=` on a memory location resolve it once, then read and
write through the address: that is what makes the target evaluated exactly
once, as solc compiles it. -/

/-- A resolved memory location: a member or an element of an object. -/
inductive Addr where
  | memoryField (id : Nat) (field : Name)
  | memoryIndex (id : Nat) (i : Int)

/-- Read the primitive value at a memory address. -/
def readLoc (s : State) : Addr -> Res Value
  | Addr.memoryField id fld => do
      match ← s.getObj id with
      | MObj.struct fields =>
          match lookupBy fld fields with
          | some v => v.asValue
          | none => .error .stuck
      | MObj.array _ => .error .stuck
  | Addr.memoryIndex id i => do
      match ← s.getObj id with
      | MObj.array elems =>
          if h : 0 ≤ i ∧ i.toNat < elems.length then
            (elems.get ⟨i.toNat, h.2⟩).asValue
          else .error .revert
      | MObj.struct _ => .error .stuck

/-- Write a primitive value at a memory address. -/
def writeLoc (s : State) (loc : Addr) (v : Value) : Res State :=
  match loc with
  | Addr.memoryField id fld => do
      match ← s.getObj id with
      | MObj.struct fields =>
          .ok (s.setObj id (MObj.struct (setBy fld v.toMVal fields)))
      | MObj.array _ => .error .stuck
  | Addr.memoryIndex id i => do
      match ← s.getObj id with
      | MObj.array elems =>
          if 0 ≤ i ∧ i.toNat < elems.length then
            .ok (s.setObj id (MObj.array (elems.set i.toNat v.toMVal)))
          else .error .revert
      | MObj.struct _ => .error .stuck

/-! ## The stores

One store per ported contract (`Syntax.lean`), in its roots' order. -/

/-- The globals of `StandardExample.sol` plus the `people` array used by the
existing worked examples. The contract starts with funds
(`selfBalance`) so the ported payment examples' transfers are covered;
insufficient-balance behavior is exercised by explicitly smaller
balances. -/
def State.exampleStore : State :=
  { selfBalance := 1000000000,
    storage :=
      [ ("total", SVal.int 0),
        ("age", SVal.int 0),
        ("owner", SVal.int 0),
        ("balance", SVal.int 0),
        ("values", SVal.array [] []),
        ("balances", SVal.map [] (SVal.int 0)),
        ("flags", SVal.map [] (SVal.bool false)),
        ("folks", SVal.map [] (defaultForRef (RefTy.struct "Person"))),
        ("matrix", SVal.array [] []),
        ("persons", SVal.array [] []),
        ("people", SVal.array [] []),
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
 -/

/-- `keyext.solidity.examples/TestSuite.sol`. Starts with funds like
`exampleStore`, for the suite's transfer tests. -/
def State.testSuiteStore : State :=
  { selfBalance := 1000000000,
    storage :=
      [ ("total", SVal.int 0),
        ("age", SVal.int 0),
        ("owner", SVal.int 0),
        ("balance", SVal.int 0),
        ("values", SVal.array [] []),
        -- `TestSuite.a : uint[]` ports to `aux`: `a` is a local `uint`
        -- in seven `SolcExpressions` functions.
        ("aux", SVal.array [] []),
        ("matrix", SVal.array [] []),
        ("balances", SVal.map [] (SVal.int 0)),
        -- `TestSuite.people : mapping(uint => Person)` ports to `folks`;
        -- `people` is already the `Person[]` of the calculus examples.
        ("folks", SVal.map [] (defaultForRef (RefTy.struct "Person"))),
        ("flags", SVal.map [] (SVal.bool false)),
        ("valuesMap", SVal.map [] (SVal.int 0)),
        ("accountMap", SVal.map [] (defaultForRef (RefTy.struct "Account"))),
        ("persons", SVal.array [] []),
        ("alice", defaultForRef (RefTy.struct "Person")),
        ("bob", defaultForRef (RefTy.struct "Person")),
        ("ledger", defaultForRef (RefTy.struct "Ledger")),
        ("tokens", SVal.array [] []),
        ("bucket", defaultForRef (RefTy.struct "TokenBucket")),
        ("ledgerUses", SVal.array [] []),
        -- Added by the re-port at solkey `c80a54494c`: the bool tier, the
        -- `Toggle` struct, the standalone `tok`, and the array/basket
        -- state the copy group writes through.
        ("flag", SVal.bool false),
        ("flag2", SVal.bool false),
        ("boolFlags", SVal.array [] []),
        ("toggle", defaultForRef (RefTy.struct "Toggle")),
        ("tok", defaultForRef (RefTy.struct "Token")),
        ("buckets", SVal.array [] []),
        ("basketA", defaultForRef (RefTy.struct "Basket")),
        ("basketB", defaultForRef (RefTy.struct "Basket")) ] }

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
        ("pairs1", SVal.array [] []),
        ("pairs2", SVal.array [] []),
        ("campaigns", SVal.map [] (defaultForRef (RefTy.struct "Simple"))) ] }

/-- `solc/SolcArrays.sol`. -/
def State.solcArraysStore : State :=
  { storage :=
      [ ("storageArray", SVal.array [] []),
        ("matrix", SVal.array [] []),
        ("structs", SVal.array [] []) ] }

/-- `solc/SolcMemory.sol`. `x` ports to `outerX` (`x` is the stack `uint`
root), `inner` to `innerS` (`inner` is a local storage alias in
`SolcStructs`), `data` to `inners` (`data` is a `Depth0` state variable
in `SolcStructs`). -/
def State.solcMemoryStore : State :=
  { storage :=
      [ ("outerX", defaultForRef (RefTy.struct "Outer")),
        ("innerS", defaultForRef (RefTy.struct "Inner")),
        ("inners", SVal.array [] []),
        ("prims", SVal.array [] []) ] }

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
        ("arrayMap", SVal.map [] (SVal.array [] [])),
        ("rows", SVal.array [] []),
        ("ledger", defaultForRef (RefTy.struct "Ledger")) ] }

/-- `solc/SolcControlFlow.sol`. -/
def State.solcControlFlowStore : State :=
  { storage :=
      [ ("sx", defaultForRef (RefTy.struct "Pair")),
        ("sy", defaultForRef (RefTy.struct "Pair")),
        ("target", defaultForRef (RefTy.struct "Pair")),
        ("values", SVal.array [] []) ] }

end Semantics

/-! ## Running a program -/

open Semantics

variable {C : Contract}

/-- The path an alias is bound to. -/
def aliasPath (σ : State) (x : Var) : Res (Name × List Seg) := do
  match ← σ.getEnv x with
  | .spath root segs => pure (root, segs)
  | .val _ | .mref _ => .error .stuck

/-- `-x` is range-checked at `int` only. -/
def unopCheck (op : UnOp) (p : PrimTy) (v : Value) : Res Value :=
  match op, p with
  | .neg, .int => checkArith .int v
  | _, _ => pure v

/-- `c ? t : e` once `c` is evaluated: the branch it picks (the other is
never evaluated). -/
def pickBranch (cv : Value) (t e : Res Value) : Res Value :=
  match cv with
  | .bool true => t
  | .bool false => e
  | .int _ => .error .stuck

/-- `a ⊕ b` on values, the right operand evaluated only when the left does not decide. -/
def evalBinop (op : BinOp) (p : PrimTy) (lv : Value) (b : Res Value) : Res Value :=
  match op, lv with
  | .and, .bool false => pure (.bool false)
  | .or, .bool true => pure (.bool true)
  | _, _ => do checkArith (op.retTy (.prim p)) (← applyBinOp op lv (← b))

/-- The value a simple value denotes: a literal, or a stack local's. -/
def Simple.eval (σ : State) {p : PrimTy} : Simple C p → Res Value
  | .lit n _ => pure (.int n)
  | .bool b => pure (.bool b)
  | .local x => do
    match ← σ.getEnv x with
    | .val v => pure v
    | .spath .. | .mref _ => .error .stuck

/-- A memory slot read as the object it references: a primitive has none. -/
def Semantics.MVal.asRef : MVal → Res Nat
  | .ref id => pure id
  | .prim _ => .error .stuck

mutual

/-- The storage path a path denotes in `σ`: `alice.account` is
`(alice, [account])`, `sp.age` whatever `sp` is bound to, then `age`. -/
def SPath.resolve (σ : State) : {T : Ty} → SPath C T → Res (Name × List Seg)
  | _, .alias x => aliasPath σ x
  | _, .loc l => l.resolve σ

def Loc.resolve (σ : State) : {T : Ty} → Loc C T → Res (Name × List Seg)
  | _, .root r _ => pure (r, [])
  | _, .field b f _ => do
    let (r, segs) ← b.resolve σ
    pure (r, segs ++ [.field f])
  | _, .index _ b i => do
    let (r, segs) ← b.resolve σ
    let i ← (← i.eval σ).asInt
    pure (r, segs ++ [.at i])

/-- The slot a memory path holds in `σ`: a memory local's reference, or
what a location holds. -/
def MPath.mval (σ : State) : {T : Ty} → MPath C T → Res MVal
  | _, .var x => do
    match ← σ.getEnv x with
    | .mref id => pure (.ref id)
    | .val _ | .spath .. => .error .stuck
  | _, .loc l => l.read σ

def MLoc.read (σ : State) : {T : Ty} → MLoc C T → Res MVal
  | _, .field b f _ => do
    let id ← (← b.mval σ).asRef
    match ← σ.getObj id with
    | .struct fields =>
      match lookupBy f fields with
      | some v => pure v
      | none => .error .stuck
    | .array _ => .error .stuck
  | _, .index b i => do
    let id ← (← b.mval σ).asRef
    let iv ← (← i.eval σ).asInt
    match ← σ.getObj id with
    | .array elems =>
      if h : 0 ≤ iv ∧ iv.toNat < elems.length then pure (elems.get ⟨iv.toNat, h.2⟩)
      else .error .revert
    | .struct _ => .error .stuck

/-- The value a value expression denotes in `σ`.  `&&` and `||` evaluate
their right operand only when the left does not decide. -/
def Val.eval (σ : State) : {p : PrimTy} → Val C p → Res Value
  | _, .simple s => s.eval σ
  | _, .read l => do
    let (r, segs) ← l.resolve σ
    (← σ.findStorage r segs).asValue
  | _, @Val.binop _ p _ op _ _ a b => do evalBinop op p (← a.eval σ) (b.eval σ)
  | _, @Val.unop _ p _ op _ _ a => do unopCheck op p (← applyUnOp op (← a.eval σ))
  | _, .ternary c a b => do pickBranch (← c.eval σ) (a.eval σ) (b.eval σ)
  | _, .readMem l => do (← l.read σ).asValue

end

/-- The storage value a source stores: a value, or the copied subtree. -/
def Src.value (σ : State) {T : Ty} : Src C T → Res SVal
  | .val v => do pure (← v.eval σ).toSVal
  | .copy p _ => do
    let (r, segs) ← p.resolve σ
    σ.findStorage r segs

/-- The default `uint x;` binds. -/
def PrimTy.default : PrimTy → Value
  | .bool => .bool false
  | .uint | .int => .int 0

/-- A write into a memory struct's member. -/
def memWriteField (σ : State) (id : Nat) (f : Name) (mv : MVal) : Res State := do
  match ← σ.getObj id with
  | .struct fields => .ok (σ.setObj id (.struct (setBy f mv fields)))
  | .array _ => .error .stuck

/-- A write into a memory array's element. -/
def memWriteIndex (σ : State) (id : Nat) (i : Int) (mv : MVal) : Res State := do
  match ← σ.getObj id with
  | .array elems =>
    if 0 ≤ i ∧ i.toNat < elems.length then .ok (σ.setObj id (.array (elems.set i.toNat mv)))
    else .error .revert
  | .struct _ => .error .stuck

/-- `l = mv` into a memory location. -/
def MLoc.write (σ : State) (mv : MVal) {T : Ty} : MLoc C T → Res State
  | .field b f _ => do
    let id ← (← b.mval σ).asRef
    memWriteField σ id f mv
  | .index b i => do
    let id ← (← b.mval σ).asRef
    let iv ← (← i.eval σ).asInt
    memWriteIndex σ id iv mv

/-- The slot a memory source writes: a value, or a reference. -/
def MSrc.mval (σ : State) {T : Ty} : MSrc C T → Res MVal
  | .val v => do pure (← v.eval σ).toMVal
  | .ref p => p.mval σ

/-- `x` bound to the object a memory right-hand side names: `n`'s by
identity, or a fresh deep copy of a storage object. -/
def MRhs.bind (σ : State) (x : Var) {R : RefTy} : MRhs C R → Res State
  | .alias p => do
    let id ← (← p.mval σ).asRef
    pure (σ.setEnv x (.mref id))
  | .copy p _ => do
    let (root, segs) ← p.resolve σ
    let sv ← σ.findStorage root segs
    let (σ', mv) ← copyStToM σ sv
    let id ← mv.asRef
    pure (σ'.setEnv x (.mref id))

/-- `a ⊕= v` at a resolved storage location: read, apply, check at the
target's type, write back. -/
def opStore (σ : State) (op : BinOp) (p : PrimTy) (root : Name) (segs : List Seg) (v : Value) :
    Res State := do
  let old ← (← σ.findStorage root segs).asValue
  let new ← applyBinOp op old v
  let new ← checkArith (.prim p) new
  σ.saveStorage root segs new.toSVal

/-- `x ⊕= v` on a stack local. -/
def opLocal (σ : State) (op : BinOp) (p : PrimTy) (x : Var) (v : Value) : Res State := do
  let old ← match ← σ.getEnv x with
    | .val v => pure v
    | .spath .. | .mref _ => .error .stuck
  let new ← applyBinOp op old v
  let new ← checkArith (.prim p) new
  pure (σ.setEnv x (.val new))

/-- `a ⊕= v` at a memory address. -/
def opMem (σ : State) (op : BinOp) (p : PrimTy) (loc : Addr) (v : Value) : Res State := do
  let old ← readLoc σ loc
  let new ← applyBinOp op old v
  let new ← checkArith (.prim p) new
  writeLoc σ loc new

/-- A compound assignment's write of `v` into its target. -/
def OpLoc.store (σ : State) (op : BinOp) : {p : PrimTy} → OpLoc C p → Value → Res State
  | p, .local x, v => opLocal σ op p x v
  | p, .root r _, v => opStore σ op p r [] v
  | p, .field b f h, v => do
    let (rt, segs) ← (Loc.field b f h).resolve σ
    opStore σ op p rt segs v
  | p, .index it b i, v => do
    let (rt, segs) ← (Loc.index it b (.simple i)).resolve σ
    opStore σ op p rt segs v
  | p, .mfield b f _, v => do
    let id ← (← b.mval σ).asRef
    opMem σ op p (.memoryField id f) v
  | p, .mindex b i, v => do
    let id ← (← b.mval σ).asRef
    let iv ← (← i.eval σ).asInt
    opMem σ op p (.memoryIndex id iv) v

/-- `x++` at a resolved storage location: read, bump, check, write back;
the value is the new one for `++x`, the old one for `x++`. -/
def bumpStore (σ : State) (op : IncDec) (p : PrimTy) (root : Name) (segs : List Seg) :
    Res (State × Value) := do
  let old ← (← σ.findStorage root segs).asValue
  let oldInt ← old.asInt
  let new ← checkArith (.prim p) (.int (if op.isIncrement then oldInt + 1 else oldInt - 1))
  let σ' ← σ.saveStorage root segs new.toSVal
  pure (σ', if op.isPre then new else old)

/-- `x++` on a stack local. -/
def bumpLocal (σ : State) (op : IncDec) (p : PrimTy) (x : Var) : Res (State × Value) := do
  let old ← match ← σ.getEnv x with
    | .val v => pure v
    | .spath .. | .mref _ => .error .stuck
  let oldInt ← old.asInt
  let new ← checkArith (.prim p) (.int (if op.isIncrement then oldInt + 1 else oldInt - 1))
  pure (σ.setEnv x (.val new), if op.isPre then new else old)

/-- `x++` at a memory address. -/
def bumpMem (σ : State) (op : IncDec) (p : PrimTy) (loc : Addr) : Res (State × Value) := do
  let old ← readLoc σ loc
  let oldInt ← old.asInt
  let new ← checkArith (.prim p) (.int (if op.isIncrement then oldInt + 1 else oldInt - 1))
  let σ' ← writeLoc σ loc new
  pure (σ', if op.isPre then new else old)

/-- `l++`: the state it leaves, and its value. -/
def OpLoc.bump (σ : State) (op : IncDec) : {p : PrimTy} → OpLoc C p → Res (State × Value)
  | p, .local x => bumpLocal σ op p x
  | p, .root r _ => bumpStore σ op p r []
  | p, .field b f h => do
    let (rt, segs) ← (Loc.field b f h).resolve σ
    bumpStore σ op p rt segs
  | p, .index it b i => do
    let (rt, segs) ← (Loc.index it b (.simple i)).resolve σ
    bumpStore σ op p rt segs
  | p, .mfield b f _ => do
    let id ← (← b.mval σ).asRef
    bumpMem σ op p (.memoryField id f)
  | p, .mindex b i => do
    let id ← (← b.mval σ).asRef
    let iv ← (← i.eval σ).asInt
    bumpMem σ op p (.memoryIndex id iv)

/-- `push` at a resolved array: the element `val` gives (from the slot the
push lands on) appended. -/
def pushAt (σ : State) (E : Ty) (root : Name) (segs : List Seg) (val : SVal → Res SVal) :
    Res State := do
  match ← σ.findStorage root segs with
  | .array elems shadow =>
    let (slot, shadow') := pushSlot E shadow
    let newElem ← val slot
    σ.saveStorage root segs (.array (elems ++ [newElem]) shadow')
  | .prim _ | .struct _ | .map _ _ => .error .stuck

/-- `b.push()` as a place: the slot appended, and its index. -/
def pushPlaceAt (σ : State) (E : Ty) (root : Name) (segs : List Seg) : Res (State × Int) := do
  match ← σ.findStorage root segs with
  | .array elems shadow =>
    let (slot, shadow') := pushSlot E shadow
    let σ' ← σ.saveStorage root segs (.array (elems ++ [slot]) shadow')
    pure (σ', elems.length)
  | .prim _ | .struct _ | .map _ _ => .error .stuck

/-- What a push appends: its argument, or the slot. -/
def Src.pushVal (σ : State) {T : Ty} : Option (Src C T) → SVal → Res SVal
  | none, slot => pure slot
  | some r, _ => r.value σ

/-- `pop` at a resolved array: the last element cleared into the shadow. -/
def popAt (σ : State) (root : Name) (segs : List Seg) : Res State := do
  match ← σ.findStorage root segs with
  | .array elems shadow =>
    match elems.reverse with
    | [] => .error .revert
    | last :: restRev => σ.saveStorage root segs (.array restRev.reverse (last.defaultOf :: shadow))
  | .prim _ | .struct _ | .map _ _ => .error .stuck

/-- `a.transfer(v)` with both evaluated: revert when the contract's funds
cannot cover `v`, else book the debit. -/
def transferAt (σ : State) (addr amt : Int) : Res State :=
  if amt < 0 then .error .stuck
  else if σ.selfBalance < amt then .error .revert
  else .ok { σ.setNet addr (σ.getNet addr - amt) with selfBalance := σ.selfBalance - amt }

/-- An alias bound to what `r` names: a path, or the slot a push appends. -/
def ARhs.bind (σ : State) (x : Var) {R : RefTy} : ARhs C R → Res State
  | .path p => do
    let (root, segs) ← p.resolve σ
    pure (σ.setEnv x (.spath root segs))
  | .push b _ => do
    let (root, segs) ← b.resolve σ
    let (σ', n) ← pushPlaceAt σ (.ref R) root segs
    pure (σ'.setEnv x (.spath root (segs ++ [.at n])))

/-- A condition's outcome: `true` goes on, `false` reverts. -/
def guard (v : Value) (σ : State) : Res State :=
  match v with
  | .bool true => pure σ
  | .bool false => .error .revert
  | .int _ => .error .stuck

mutual

/-- The state a statement leaves, from `σ`: `alice.age = 10;` saves `10` at
`alice.age`, `Person storage p = alice;` binds `p` to `alice`'s path. -/
def Stmt.run (σ : State) : Stmt C → Res State
  | .assign l r => do
    let sv ← r.value σ
    let (root, segs) ← l.resolve σ
    σ.saveStorage root segs sv
  | .rebind x r => r.bind σ x
  | .assignLocal x r => do pure (σ.setEnv x (.val (← r.eval σ)))
  | .declLocal p x init => do
    let v ← match init with
      | none => pure (PrimTy.default p)
      | some e => e.eval σ
    pure (σ.setEnv x (.val v))
  | .declStorage _ x init =>
    match init with
    | none => pure σ
    | some r => r.bind σ x
  | .declMem R x init _ => do
    match init with
    | none =>
      let (σ', id) ← allocDefault σ R
      pure (σ'.setEnv x (.mref id))
    | some r => r.bind σ x
  | .rebindMem x r => r.bind σ x
  | .assignMem l r => do l.write σ (← r.mval σ)
  | .assignFromMem l p => do
    let sv ← copyMem σ (← p.mval σ)
    let (root, segs) ← l.resolve σ
    σ.saveStorage root segs sv
  | .opAssign op _ _ l r => do l.store σ op (← r.eval σ)
  | .incDec op _ l => do pure (← l.bump σ op).1
  | .assignIncDec x op _ l _ => do
    let (σ', v) ← l.bump σ op
    pure (σ'.setEnv x (.val v))
  | .push (E := E) b v _ => do
    let (root, segs) ← b.resolve σ
    pushAt σ E root segs (Src.pushVal σ v)
  | .pop b => do
    let (root, segs) ← b.resolve σ
    popAt σ root segs
  | .transfer r a => do
    let addr ← (← r.eval σ).asInt
    let amt ← (← a.eval σ).asInt
    transferAt σ addr amt
  | .delete l => do
    let (root, segs) ← l.resolve σ
    let cur ← σ.findStorage root segs
    σ.saveStorage root segs cur.defaultOf
  | .ite c thn els => do
    match ← c.eval σ with
    | .bool true => Prog.run σ thn
    | .bool false => Prog.run σ els
    | .int _ => .error .stuck
  | .require c => do guard (← c.eval σ) σ
  | .assert c => do guard (← c.eval σ) σ
  | .revert => .error .revert

/-- The state a block leaves. -/
def Prog.run (σ : State) : List (Stmt C) → Res State
  | [] => pure σ
  | s :: P => do Prog.run (← s.run σ) P

end

/-! ## Each contract starts in its store -/

/-- The storage a contract starts with: each root at its type's default. -/
def Contract.initStorage (C : Contract) : List (Name × SVal) :=
  C.vars.map fun (n, T) => (n, defaultForTy T)

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

/-! ## Examples

A program run on `StandardExample`'s store. -/

section Examples

local instance : InContract := ⟨StandardExample⟩

/-- `x = 10` through an alias. -/
def aliasWrite : Prog StandardExample := sol{
  Person storage p = alice; p.age = 10; uint x = alice.age; assert(x == 10);
}

/-- info: Except.ok (Solidity.Semantics.SVal.prim (Solidity.Semantics.PrimVal.int 10)) -/
#guard_msgs in
#eval (do (← Prog.run State.exampleStore aliasWrite).findStorage "alice" [.field "age"] : Res SVal)

/-- A failing guard reverts. -/
example : (Prog.run State.exampleStore (sol{ require(age > 3); } : Prog StandardExample)) =
    .error .revert := rfl

end Examples

end Solidity
