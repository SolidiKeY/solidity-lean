import Solidity.Syntax

/-!
# The interpreter

What a program does, the reference every rule is proved sound against
(mini-solkey's `Ch04_Semantics`).  The state is KeY's: a storage tree
(`structRules.key`), an identity-indexed memory heap (`memoryRules.key`),
the locals, the `net` payment ledger and the contract's funds
(`netHeader.key`), and the transaction's environment (`msg.sender`, …).  `Stmt.run`
runs a statement on it by structural recursion on the typed syntax, so
every function here terminates and every branch on a type was already
taken by the index.

Semantic conventions mirrored from KeY:
- storage assignment copies by value (`save`/`select`/`store`), memory
  assignment aliases identities, cross-domain assignments deep-copy
  (`copySt`/`copyMem`);
- array reads and writes out of bounds revert; `pop()` on an empty array
  reverts; `/` and `%` revert on a zero divisor; a failing `assert`
  panics (below);
- `a.transfer(v)` books `net(a) := net(a) - v` unless `a` is the contract
  itself, which books nothing (solkey's `\if(a = self)`), with no callback
  (the callback reading is `Semantics/Callback.lean`'s, a relation over this
  one), and nothing else: the contract is assumed able to pay, and its funds
  (`State.selfBalance`) are not the transfer's to change.  Whether the EVM
  pays is the compiler theorem's business (`Evm/Correctness.lean`, where a
  refused payment is a revert of the machine alone);
- `pv = a.send(v);` books as `transfer` does and sets `pv` to `true` when the
  recipient takes the payment, and books nothing and sets `pv` to `false`
  when it refuses (`sendAt`): which, the transaction's oracle says
  (`TxEnv.ext`), as it does for a `try`;
- a call runs its inlined body (`Stmt.call`, KeY's `functionBodyExpand`):
  its arguments read in the caller's state, bound to its parameters, its
  return variable declared, the body run, the result assigned;
- an external call (`try`) runs no callee: how it ends is the transaction's
  (`TxEnv.ext`), and its clause's block runs in the caller's state, the
  returned data or the `Panic` code bound first.

Where solc and KeY differ on an external call, this follows solc: a call to an
address with no code, and returned data that does not decode, revert in the
caller, which no `catch` clause catches.

Semantic conventions mirrored from solc, where KeY was more liberal
(`docs/solc-alignment.md`):
- arithmetic is **checked** (solc ≥ 0.8): a result outside its type's
  range (`uint` = `uint256`, `int` = `int256`) reverts (`checkArith`);
- an assignment evaluates its **right-hand side before resolving the
  left-hand side**, and `++`/`--` and `op=` resolve their target exactly
  once;

A run ends in a state or halts: `revert` (the program reverted), `panic`
(an `assert` failed: solc's `Panic(0x01)`, KeY's `assertSimple` "Violated"
branch, which no modality accepts), or `stuck` (a state that does not fit the
program, e.g. a local read before it is bound).  solc's other panics
(overflow, a zero divisor, an index out of bounds, `pop()` on an empty array)
are reverts here, as in KeY, where a box accepts them.  The copy from memory back to storage terminates on the visited-set
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
  length — beside the slots past the end.  `shadow k` is the content of slot
  `elems.length + k`: what a `pop`, a `delete` or a shorter copy cleared and
  left behind, and what a write through a reference to a popped element put
  there.  The slots are storage like any other (solc: nothing is freed), so a
  reference to one still reads and writes it, and the next `push` of a struct
  lands on it as it is (`storagePushLengthSaveReferenceElement`); `delete`
  never clears a mapping member, so a mapping nested in a popped element
  survives into that `push` too.

  `fixed` marks a fixed-size array (`uint[3]`, KeY's `typed(fixedArr(n, sh),
  st)`): its length never changes, so `delete` resets its elements in place
  rather than emptying it (`delNodeFixed`), and a copy over it keeps it
  fixed.  Nothing else reads the mark: a fixed array is indexed, bounds-checked
  and copied like a dynamic one. -/
  | array (elems : List SVal) (shadow : List SVal) (fixed : Bool)
  | map (entries : List (Int × SVal)) (dflt : SVal)
  deriving Repr

/-! `SVal`'s equality is decidable, written out by hand (a nested
inductive): `Binding` holds a storage (`Binding.store`) and derives its
`DecidableEq`. -/
mutual

private def svalDecEq : (a b : SVal) -> Decidable (a = b)
  | .prim x, .prim y =>
      if h : x = y then .isTrue (by rw [h])
      else .isFalse (fun he => h (SVal.prim.inj he))
  | .struct fs, .struct gs =>
      match svalFieldsDecEq fs gs with
      | .isTrue h => .isTrue (by rw [h])
      | .isFalse h => .isFalse (fun he => h (SVal.struct.inj he))
  | .array xs sx fx, .array ys sy fy =>
      if h3 : fx = fy then
        match svalElemsDecEq xs ys, svalElemsDecEq sx sy with
        | .isTrue h1, .isTrue h2 => .isTrue (by rw [h1, h2, h3])
        | .isFalse h1, _ => .isFalse (fun he => h1 (SVal.array.inj he).1)
        | _, .isFalse h2 => .isFalse (fun he => h2 (SVal.array.inj he).2.1)
      else .isFalse (fun he => h3 (SVal.array.inj he).2.2)
  | .map es d, .map fs e =>
      match svalEntriesDecEq es fs, svalDecEq d e with
      | .isTrue h1, .isTrue h2 => .isTrue (by rw [h1, h2])
      | .isFalse h1, _ => .isFalse (fun he => h1 (SVal.map.inj he).1)
      | _, .isFalse h2 => .isFalse (fun he => h2 (SVal.map.inj he).2)
  | .prim _, .struct _ => .isFalse (fun he => SVal.noConfusion he)
  | .prim _, .array _ _ _ => .isFalse (fun he => SVal.noConfusion he)
  | .prim _, .map _ _ => .isFalse (fun he => SVal.noConfusion he)
  | .struct _, .prim _ => .isFalse (fun he => SVal.noConfusion he)
  | .struct _, .array _ _ _ => .isFalse (fun he => SVal.noConfusion he)
  | .struct _, .map _ _ => .isFalse (fun he => SVal.noConfusion he)
  | .array _ _ _, .prim _ => .isFalse (fun he => SVal.noConfusion he)
  | .array _ _ _, .struct _ => .isFalse (fun he => SVal.noConfusion he)
  | .array _ _ _, .map _ _ => .isFalse (fun he => SVal.noConfusion he)
  | .map _ _, .prim _ => .isFalse (fun he => SVal.noConfusion he)
  | .map _ _, .struct _ => .isFalse (fun he => SVal.noConfusion he)
  | .map _ _, .array _ _ _ => .isFalse (fun he => SVal.noConfusion he)

private def svalFieldsDecEq :
    (a b : List (Name × SVal)) -> Decidable (a = b)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (fun he => List.noConfusion he)
  | _ :: _, [] => .isFalse (fun he => List.noConfusion he)
  | (n, v) :: xs, (m, w) :: ys =>
      if hn : n = m then
        match svalDecEq v w, svalFieldsDecEq xs ys with
        | .isTrue hv, .isTrue ht => .isTrue (by rw [hn, hv, ht])
        | .isFalse hv, _ =>
            .isFalse (fun he =>
              hv (Prod.mk.inj (List.cons.inj he).1).2)
        | _, .isFalse ht =>
            .isFalse (fun he => ht (List.cons.inj he).2)
      else
        .isFalse (fun he => hn (Prod.mk.inj (List.cons.inj he).1).1)

private def svalElemsDecEq : (a b : List SVal) -> Decidable (a = b)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (fun he => List.noConfusion he)
  | _ :: _, [] => .isFalse (fun he => List.noConfusion he)
  | x :: xs, y :: ys =>
      match svalDecEq x y, svalElemsDecEq xs ys with
      | .isTrue hx, .isTrue ht => .isTrue (by rw [hx, ht])
      | .isFalse hx, _ =>
          .isFalse (fun he => hx (List.cons.inj he).1)
      | _, .isFalse ht =>
          .isFalse (fun he => ht (List.cons.inj he).2)

private def svalEntriesDecEq :
    (a b : List (Int × SVal)) -> Decidable (a = b)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (fun he => List.noConfusion he)
  | _ :: _, [] => .isFalse (fun he => List.noConfusion he)
  | (i, v) :: xs, (j, w) :: ys =>
      if hi : i = j then
        match svalDecEq v w, svalEntriesDecEq xs ys with
        | .isTrue hv, .isTrue ht => .isTrue (by rw [hi, hv, ht])
        | .isFalse hv, _ =>
            .isFalse (fun he =>
              hv (Prod.mk.inj (List.cons.inj he).1).2)
        | _, .isFalse ht =>
            .isFalse (fun he => ht (List.cons.inj he).2)
      else
        .isFalse (fun he => hi (Prod.mk.inj (List.cons.inj he).1).1)

end

instance : DecidableEq SVal := svalDecEq

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

/-- Memory objects, one per identity (`memoryRules.key`).  An array carries
whether it is a fixed-size one, as a storage array does, so that a copy back
to storage lands as the same kind (`copyMToSt`). -/
inductive MObj where
  | struct (fields : List (Name × MVal))
  | array (elems : List MVal) (fixed : Bool)
  deriving Repr

/-- One step of a storage path: a field or an `at(i)` selector
(array index or mapping key). -/
inductive Seg where
  | field (name : Name)
  | at (i : Int)
  deriving Repr, DecidableEq

/-- Local bindings: stack values, storage path aliases, memory
references, and a whole storage (KeY's program variable `old` of sort
`Struct`, which a specification's `\old` reads; no statement binds one). -/
inductive Binding where
  | val (v : Value)
  | spath (root : Name) (segs : List Seg)
  | mref (id : Nat)
  | store (st : List (Name × SVal))
  /-- A whole ledger: KeY's `oldNet`, which a specification's `\old(net(a))`
  reads; no statement binds one either. -/
  | ledger (l : List (Int × Int))
  deriving Repr, DecidableEq

/-- How an external call ends, as its caller sees it: it returns this data,
or it reverts with `Error(string)`, with `Panic(uint)` and this code, or in
another way. -/
inductive ExtResult where
  | ok (data : List Value)
  | error
  | panic (code : Value)
  | other
  deriving Repr, DecidableEq

/-- An external call as it is made: the callee's address, the function, the
arguments' values. -/
structure ExtKey where
  addr : Int
  fn : String
  args : List Value
  deriving Repr, DecidableEq

/-- What the transaction running the program was sent with: KeY's program
variables `msgSender` and `msgValue` (`netHeader.key`) and the block's
timestamp; and how each external call it makes ends (`ext`), a call it has
no entry for reaching an address with no code (which a `try` reverts on, and
a `send` pays: `sendAt`).  Two identical calls, or two `send`s of one amount
to one address, read the same entry.  No statement changes them,
and a callback leaves them as they were (`State.havoc`): a re-entrant call
runs in its own transaction, which the caller never sees.  The calculus
reads none of `ext`: a `try` has a goal for every way its call may end
(`tryCallNoCallbackBox`), a `send` one for each outcome
(`sendNoCallbackBox`), so a proof holds whatever the table says. -/
structure TxEnv where
  msgSender : Int := 0
  /-- The contract's own address, `address(this)`: the ledger's own account. -/
  selfAddress : Int := 0
  msgValue : Int := 0
  timestamp : Int := 0
  ext : List (ExtKey × ExtResult) := []
  deriving Repr, DecidableEq

structure State where
  storage : List (Name × SVal)
  heap : List (Nat × MObj) := []
  nextId : Nat := 0
  env : List (Var × Binding) := []
  net : List (Int × Int) := []
  /-- The contract's own funds (`address(this).balance`), as the
  transaction found them, `msg.value` booked by a `payable` function's
  specification (`Calculus/Spec.lean`).  A `transfer` books `net` only and
  leaves them. -/
  selfBalance : Int := 0
  /-- `msg.sender`, `msg.value`, `block.timestamp`. -/
  tx : TxEnv := {}
  deriving Repr

inductive Halt where
  | revert
  | stuck
  | panic
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
  | Ty.ref (RefTy.array _) => SVal.array [] [] false
  | Ty.ref (RefTy.fixed E n) => SVal.array (List.replicate n (defaultForTy E)) [] true
  | Ty.ref (RefTy.mapping _ value) => SVal.map [] (defaultForTy value)
termination_by ty => (tyRank ty, sizeOf ty)
decreasing_by
  · exact Prod.Lex.left _ _ (structDef_rank_lt _)
  all_goals first
    | (apply Prod.Lex.left; simp [tyRank]; done)
    | (apply Prod.Lex.right; simp; omega)

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
`delete` resets primitives, recurses into struct fields and array elements —
but leaves mappings untouched (entries and default), the Solidity `delete`
semantics solkey implements with the lazy `delNode` marker
(`selectStDelNodeMap` reads mapping members through to the original). A
direct `delete` on a mapping is a solc compile error, so the no-op `map` arm
is unreachable from real programs.

An array is emptied: its length is `0`, and its live elements are cleared
into the slots past the end, in place, where the slots already there stay
as they are.  That is solc (the element slots are cleared, the mapping
entries nested in them live on at hashed slots nothing clears, so
`delete arr; arr.push();` sees them again) and, since `f2eb3d98eb`, solkey:
`selectStDelNodeIndexStruct` reads an index of a deleted node below its old
`size` as the element deleted and one past it as it was.

A fixed-size array keeps its length: its elements are reset in place
(solc; solkey's `delNodeFixed`, `selectStDelNodeFixed{Element,Size,Value}`). -/
def SVal.defaultOf : SVal -> SVal
  | SVal.int _ => SVal.int 0
  | SVal.bool _ => SVal.bool false
  | SVal.struct fields => SVal.struct (defaultOfFields fields)
  | SVal.array elems shadow false => SVal.array [] (defaultOfElems elems ++ shadow) false
  | SVal.array elems shadow true => SVal.array (defaultOfElems elems) shadow true
  | SVal.map entries dflt => SVal.map entries dflt
where
  defaultOfFields : List (Name × SVal) -> List (Name × SVal)
  | [] => []
  | (name, v) :: rest => (name, v.defaultOf) :: defaultOfFields rest
  defaultOfElems : List SVal -> List SVal
  | [] => []
  | v :: rest => v.defaultOf :: defaultOfElems rest

/-- A value written to slots nothing has written before: its arrays have
nothing past their ends (a copy copies the live elements only). -/
def SVal.strip : SVal -> SVal
  | SVal.prim p => SVal.prim p
  | SVal.struct fields => SVal.struct (stripFields fields)
  | SVal.array elems _ fx => SVal.array (stripElems elems) [] fx
  | SVal.map entries dflt => SVal.map entries dflt
where
  stripFields : List (Name × SVal) -> List (Name × SVal)
  | [] => []
  | (name, v) :: rest => (name, v.strip) :: stripFields rest
  stripElems : List SVal -> List SVal
  | [] => []
  | v :: rest => v.strip :: stripElems rest

/-- A copy of `new` written over `old` (a storage-to-storage or a
memory-to-storage copy of a struct or an array, or a `push` of one onto a
recycled slot): what the slots hold afterwards.  Primitives are `new`'s; a
struct's members are copied member by member; an array takes `new`'s length
and elements, each copied over the slot it lands on, and the old slots past
the new length are cleared (`defaultOf`) up to the old length and left as
they were beyond it.  That is solc's copy, and solkey's since `f2eb3d98eb`
(`selectOnSaveEmptyIndexStruct`: below the new `size` the element saved over
the old one, below the old `size` the old one deleted, beyond both the old
one).  An array is `new`'s kind of array, fixed-size or dynamic (a memory
array carries its kind, `MObj.array`, so a copy from memory lands as the kind
it was allocated as).  Onto a slot of another shape, or none, `new` lands as
on fresh storage (`SVal.strip`).  A mapping is never copied (a copy is `mapFree`),
and one met here keeps the old entries (`selectOnSaveEmptyMap`). -/
def SVal.overlay : SVal -> SVal -> SVal
  | SVal.struct ofs, SVal.struct nfs => SVal.struct (overlayFields ofs nfs)
  | SVal.array oel osh _, SVal.array nel _ nfx =>
    SVal.array (overlayElems (oel ++ osh) nel)
      (SVal.defaultOf.defaultOfElems (oel.drop nel.length) ++ osh.drop (nel.length - oel.length))
      nfx
  | SVal.map oe od, SVal.map _ _ => SVal.map oe od
  | _, new => new.strip
where
  overlayFields (ofs : List (Name × SVal)) : List (Name × SVal) -> List (Name × SVal)
  | [] => []
  | (name, v) :: rest =>
    (name, match lookupBy name ofs with
      | some o => o.overlay v
      | none => v.strip) :: overlayFields ofs rest
  overlayElems : List SVal -> List SVal -> List SVal
  | o :: os, v :: rest => o.overlay v :: overlayElems os rest
  | [], rest => SVal.strip.stripElems rest
  | _ :: _, [] => []

/-- The slot `arr.push()` lands on, and the slots past the end that are
left: the first of them as it is, or a fresh default where the array has
never been that long.  A primitive element is cleared first (KeY writes
`delAt(storage, at(n))`, `storagePushLengthSave`); a struct or an array is
not (`storagePushLengthSaveReferenceElement`): solc's `push()` does not zero
the slot, which a `pop` cleared already, so a value written there through a
reference to the popped element is seen again, and so is a mapping nested in
it.

`push(se)` and `push(sp)` write their value to the slot instead, as on
fresh slots (`Src.pushVal`, `SVal.strip`).  They still *consume* the slot,
since it becomes live again.  (solc copies the value member by member over
the recycled slot, so the one difference is past the end of an array nested
in the element, which only a write through a reference to a popped element
can have dirtied.)

The `isPrimitive` branch is **redundant on any well-typed storage**, where a
cleared primitive slot *is* the type's default (`pushSlot_prim`, proved in
`Typing/StoragePreservation.lean`); it is written out so that a consumer holding a
value *representation* but no typing — the removed EVM compiler's
correctness proof, whose fragment was primitive-element arrays — sees the
pushed value without a typing hypothesis. -/
def pushSlot (elemTy : Ty) : List SVal -> SVal × List SVal
  | [] => (defaultForTy elemTy, [])
  | c :: rest =>
      (if elemTy.isPrimitive then defaultForTy elemTy else c, rest)

/-- At a primitive element type the slot a `push` lands on is the type's
default, recycled or not — what the removed EVM compiler's correctness proof
read off it. -/
theorem pushSlot_isPrim {elemTy : Ty} {shadow : List SVal}
    (hp : elemTy.isPrimitive = true) :
    (pushSlot elemTy shadow).1 = defaultForTy elemTy := by
  cases shadow <;> simp [pushSlot, hp]

/-! ## Storage find / save -/

/-! A path's segments address *slots*: `Seg.at i` into an array is its
`i`-th slot, a live element or one past the end (the `shadow`).  Whether an
index is in bounds is checked where the program takes it (`State.checkIndex`,
in `Loc.resolve` and `Tm.eval`), not here, so that a reference bound to an
element keeps addressing its slot after a `pop` (solc). -/

def SVal.find : SVal -> List Seg -> Res SVal
  | v, [] => .ok v
  | SVal.struct fields, Seg.field name :: rest =>
      match lookupBy name fields with
      | some v => v.find rest
      | none => .error .stuck
  | SVal.array elems shadow _, Seg.at i :: rest =>
      if h : 0 ≤ i ∧ i.toNat < (elems ++ shadow).length then
        ((elems ++ shadow).get ⟨i.toNat, h.2⟩).find rest
      else .error .revert
  -- `a.length`: solkey's suites assert array lengths directly
  -- (`assert(values.length == 3)`), and the parser gives `.length` a
  -- `Seg.field`, so it has to be answered here rather than by the struct
  -- arm above — an array is not a struct with a `length` member.  A
  -- fixed-size array has no `length` slot: its length is its type's (KeY's
  -- `selectOnTypedFixedSize`), and a program's `.length` of one is a literal.
  | SVal.array elems _ fx, Seg.field "length" :: rest =>
      if fx then .error .stuck else (SVal.int elems.length).find rest
  | SVal.map entries dflt, Seg.at i :: rest =>
      match lookupBy i entries with
      | some v => v.find rest
      | none => dflt.find rest
  -- The shape mismatches, enumerated rather than left to a wildcard: a
  -- primitive under any selector, a struct under `at`, an array under a
  -- field other than the `length` arm above, a mapping under a field.
  | SVal.prim _, _ :: _ => .error .stuck
  | SVal.struct _, Seg.at _ :: _ => .error .stuck
  | SVal.array _ _ _, Seg.field _ :: _ => .error .stuck
  | SVal.map _ _, Seg.field _ :: _ => .error .stuck

def SVal.save : SVal -> List Seg -> SVal -> Res SVal
  | _, [], new => .ok new
  | SVal.struct fields, Seg.field name :: rest, new =>
      match lookupBy name fields with
      | some old => do
          let updated ← old.save rest new
          .ok (SVal.struct (setBy name updated fields))
      | none => .error .stuck
  | SVal.array elems shadow fx, Seg.at i :: rest, new =>
      if h : 0 ≤ i ∧ i.toNat < (elems ++ shadow).length then do
        let updated ← ((elems ++ shadow).get ⟨i.toNat, h.2⟩).save rest new
        let slots := (elems ++ shadow).set i.toNat updated
        .ok (SVal.array (slots.take elems.length) (slots.drop elems.length) fx)
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
  | SVal.array _ _ _, Seg.field _ :: _, _ => .error .stuck
  | SVal.map _ _, Seg.field _ :: _, _ => .error .stuck

/-- A read that checks every index against the live length, as a program
path's resolution does (`State.checkIndex` in `Loc.resolve`) before the slot
is read: on a path a program resolved it is `find`, and past the end it
reverts where `find` would read the slot.  The EVM compiler states what its
storage holds with it (`Evm.compile_storage`), and `sol_decide` reads with it
(`Calculus/Decide.lean`). -/
def SVal.findLive : SVal -> List Seg -> Res SVal
  | v, [] => .ok v
  | SVal.struct fields, Seg.field name :: rest =>
      match lookupBy name fields with
      | some v => v.findLive rest
      | none => .error .stuck
  | SVal.array elems _ _, Seg.at i :: rest =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then
        (elems.get ⟨i.toNat, h.2⟩).findLive rest
      else .error .revert
  | SVal.array elems _ fx, Seg.field "length" :: rest =>
      if fx then .error .stuck else (SVal.int elems.length).findLive rest
  | SVal.map entries dflt, Seg.at i :: rest =>
      match lookupBy i entries with
      | some v => v.findLive rest
      | none => dflt.findLive rest
  | SVal.prim _, _ :: _ => .error .stuck
  | SVal.struct _, Seg.at _ :: _ => .error .stuck
  | SVal.array _ _ _, Seg.field _ :: _ => .error .stuck
  | SVal.map _ _, Seg.field _ :: _ => .error .stuck

namespace State

def findStorage (s : State) (root : Name) (segs : List Seg) : Res SVal :=
  match lookupBy root s.storage with
  | some v => v.find segs
  | none => .error .stuck

/-- `SVal.findLive` at a root. -/
def findLive (s : State) (root : Name) (segs : List Seg) : Res SVal :=
  match lookupBy root s.storage with
  | some v => v.findLive segs
  | none => .error .stuck

def saveStorage (s : State) (root : Name) (segs : List Seg) (new : SVal) :
    Res State :=
  match lookupBy root s.storage with
  | some v => do
      let updated ← v.save segs new
      .ok { s with storage := setBy root updated s.storage }
  | none => .error .stuck

/-- `arr[i]` is in bounds where the program takes the index: solc's
`Panic(0x32)`, checked once, when the path is resolved (a read, a write, an
alias bound), and not again when an alias bound to the element is used.  A
mapping takes every key; a word or a struct takes none (no typed program
indexes one). -/
def checkIndex (s : State) (root : Name) (segs : List Seg) (i : Int) : Res Unit := do
  match ← s.findStorage root segs with
  | .array elems _ _ => if 0 ≤ i ∧ i.toNat < elems.length then pure () else .error .revert
  | .map _ _ => pure ()
  | .prim _ | .struct _ => .error .stuck

/-- A storage write of what an assignment's right-hand side denotes: a word
is stored; a struct or an array is copied over what is there
(`SVal.overlay`). -/
def writeStorage (s : State) (root : Name) (segs : List Seg) (new : SVal) : Res State :=
  match new with
  | .prim p => s.saveStorage root segs (.prim p)
  | .struct _ | .array .. | .map .. => do
    let cur ← s.findStorage root segs
    s.saveStorage root segs (cur.overlay new)

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

/-- A value of the environment: `msg.sender` is `tx.msgSender`,
`address(this).balance` the funds `transfer` debits. -/
def envVal (s : State) : EnvKey → Int
  | .msgSender => s.tx.msgSender
  | .msgValue => s.tx.msgValue
  | .timestamp => s.tx.timestamp
  | .selfBalance => s.selfBalance
  | .selfAddress => s.tx.selfAddress

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
  | SVal.array elems _ fx => do
      let (s, melems) ← copyStElems s elems
      let (s, id) := s.alloc (MObj.array melems fx)
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
        | .ok (MObj.array elems fx) => do
            let selems ← copyMElems s (rem.erase id) elems
            .ok (SVal.array selems [] fx)
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
  | SVal.array _ _ _ => .error .stuck
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

/-- `2^256`, the exclusive upper bound of `uint256` (cast from `Nat`,
where kernel arithmetic on the literal is fast). -/
def uintBound : Int := ((2 ^ 256 : Nat) : Int)

/-- `&&&`, `|||` or `^^^` on two `uint` words, behind a match on the operands:
the kernel meets `Nat.land` only on numerals, where it computes it, and never
unfolds it (well-founded recursion, a deep-recursion error), even when an
operand is still a read of the state.  A negative operand, which `uint`
rules out, gives `0`. -/
def uintBitwise (f : Nat → Nat → Nat) : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (f a b)
  | _, _ => 0

theorem uintBitwise_natCast (f : Nat → Nat → Nat) (a b : Nat) :
    uintBitwise f (a : Int) (b : Int) = ((f a b : Nat) : Int) := rfl

/-- Arithmetic and relational operators on values. `/` and `%` revert on
a zero divisor (KeY `divisionAssignment`/`moduloAssignment`); `**` with a
negative exponent is stuck.  The bitwise operators, the shifts and the
wrapping arithmetic are solc's at `uint256`: `~x` is `2^256 - 1 - x`,
`x << n` is `x * 2^n` modulo `2^256`, `x >> n` is `x / 2^n`, a shift by
`256` or more gives `0`, and `+%` (what `unchecked { a + b; }` is) is `a + b`
modulo `2^256`. -/
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
  -- the `uint` operators with no overflow to check (`BinOp.accepts`): their
  -- result is below `2^256` already, so `checkArith` passes it
  | .band => do .ok (Value.int (uintBitwise (· &&& ·) (← l.asInt) (← r.asInt)))
  | .bor => do .ok (Value.int (uintBitwise (· ||| ·) (← l.asInt) (← r.asInt)))
  | .bxor => do .ok (Value.int (uintBitwise (· ^^^ ·) (← l.asInt) (← r.asInt)))
  | .shl => do
      let a ← l.asInt
      let n ← r.asInt
      .ok (Value.int (if n < 256 then a * 2 ^ n.toNat % uintBound else 0))
  | .shr => do
      let a ← l.asInt
      let n ← r.asInt
      .ok (Value.int (if n < 256 then a / 2 ^ n.toNat else 0))
  | .addW => do .ok (Value.int (((← l.asInt) + (← r.asInt)) % uintBound))
  | .subW => do .ok (Value.int (((← l.asInt) - (← r.asInt)) % uintBound))
  | .mulW => do .ok (Value.int ((← l.asInt) * (← r.asInt) % uintBound))
  | .powW => do
      let b ← l.asInt
      let e ← r.asInt
      if e < 0 then .error .stuck else .ok (Value.int (b ^ e.toNat % uintBound))

def applyUnOp (op : UnOp) (v : Value) : Res Value :=
  match op with
  | .neg => do .ok (Value.int (-(← v.asInt)))
  | .not => do .ok (Value.bool (!(← v.asBool)))
  | .bnot => do .ok (Value.int (uintBound - 1 - (← v.asInt)))

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
      | MObj.array _ _ => .error .stuck
  | Addr.memoryIndex id i => do
      match ← s.getObj id with
      | MObj.array elems _ =>
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
      | MObj.array _ _ => .error .stuck
  | Addr.memoryIndex id i => do
      match ← s.getObj id with
      | MObj.array elems fx =>
          if 0 ≤ i ∧ i.toNat < elems.length then
            .ok (s.setObj id (MObj.array (elems.set i.toNat v.toMVal) fx))
          else .error .revert
      | MObj.struct _ => .error .stuck

/-! ## The stores

One store per ported contract (`Syntax.lean`), in its roots' order. -/

/-- The globals of `StandardExample.sol` plus the `people` array used by the
existing worked examples, with funds (`selfBalance`) for
`address(this).balance` to read. -/
def State.exampleStore : State :=
  { selfBalance := 1000000000,
    storage :=
      [ ("total", SVal.int 0),
        ("age", SVal.int 0),
        ("owner", SVal.int 0),
        ("balance", SVal.int 0),
        ("values", SVal.array [] [] false),
        ("balances", SVal.map [] (SVal.int 0)),
        ("flags", SVal.map [] (SVal.bool false)),
        ("folks", SVal.map [] (defaultForRef (RefTy.struct "Person"))),
        ("matrix", SVal.array [] [] false),
        ("persons", SVal.array [] [] false),
        ("people", SVal.array [] [] false),
        ("alice", defaultForRef (RefTy.struct "Person")),
        ("bob", defaultForRef (RefTy.struct "Person")),
        ("wallet", defaultForRef (RefTy.struct "Wallet")) ] }

/-! ### Stores of the ported solkey contracts

One store per ported contract, not one union store. The store is an
association list the interpreter scans on every read and write, so its
length is a direct multiplier on the cost of every run from it: a
46-entry union of these schemas made even small judgments time out at
`whnf`. Per-contract stores are also the faithful
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
        ("values", SVal.array [] [] false),
        -- `TestSuite.a : uint[]` ports to `aux`: `a` is a local `uint`
        -- in seven `SolcExpressions` functions.
        ("aux", SVal.array [] [] false),
        ("matrix", SVal.array [] [] false),
        ("balances", SVal.map [] (SVal.int 0)),
        -- `TestSuite.people : mapping(uint => Person)` ports to `folks`;
        -- `people` is already the `Person[]` of the calculus examples.
        ("folks", SVal.map [] (defaultForRef (RefTy.struct "Person"))),
        ("flags", SVal.map [] (SVal.bool false)),
        ("valuesMap", SVal.map [] (SVal.int 0)),
        ("accountMap", SVal.map [] (defaultForRef (RefTy.struct "Account"))),
        ("persons", SVal.array [] [] false),
        ("alice", defaultForRef (RefTy.struct "Person")),
        ("bob", defaultForRef (RefTy.struct "Person")),
        ("ledger", defaultForRef (RefTy.struct "Ledger")),
        ("tokens", SVal.array [] [] false),
        ("bucket", defaultForRef (RefTy.struct "TokenBucket")),
        ("ledgerUses", SVal.array [] [] false),
        -- Added by the re-port at solkey `c80a54494c`: the bool tier, the
        -- `Toggle` struct, the standalone `tok`, and the array/basket
        -- state the copy group writes through.
        ("flag", SVal.bool false),
        ("flag2", SVal.bool false),
        ("boolFlags", SVal.array [] [] false),
        ("toggle", defaultForRef (RefTy.struct "Toggle")),
        ("tok", defaultForRef (RefTy.struct "Token")),
        ("buckets", SVal.array [] [] false),
        ("basketA", defaultForRef (RefTy.struct "Basket")),
        ("basketB", defaultForRef (RefTy.struct "Basket")),
        -- Added with fixed-size arrays: `signedTotal`, the fixed-array state
        -- (`Triple` ported as `FixedTriple`, `structDef`) and the mapping
        -- shapes.  `boolKeyed` (a `bool` key reads as no `Int`) and `tree`
        -- (a struct recursive through a mapping outranks itself, `structRank`)
        -- are not ported.
        ("signedTotal", SVal.int 0),
        ("fixedValues", defaultForRef (RefTy.fixed Ty.uint 3)),
        ("rows", SVal.array [] [] false),
        ("fixedTokens", defaultForRef (RefTy.fixed (Ty.struct "Token") 2)),
        ("fixedMaps", defaultForRef (RefTy.fixed (Ty.mapping Ty.uint Ty.uint) 2)),
        ("triple", defaultForRef (RefTy.struct "FixedTriple")),
        ("triple2", defaultForRef (RefTy.struct "FixedTriple")),
        ("grid", SVal.map [] (SVal.map [] (SVal.int 0))),
        ("ledgerMap", SVal.map [] (defaultForRef (RefTy.struct "Ledger"))),
        ("mapArray", SVal.array [] [] false) ] }

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
        ("pairs1", SVal.array [] [] false),
        ("pairs2", SVal.array [] [] false),
        ("campaigns", SVal.map [] (defaultForRef (RefTy.struct "Simple"))) ] }

/-- `solc/SolcArrays.sol`. -/
def State.solcArraysStore : State :=
  { storage :=
      [ ("storageArray", SVal.array [] [] false),
        ("matrix", SVal.array [] [] false),
        ("structs", SVal.array [] [] false) ] }

/-- `solc/SolcMemory.sol`. `x` ports to `outerX` (`x` is the stack `uint`
root), `inner` to `innerS` (`inner` is a local storage alias in
`SolcStructs`), `data` to `inners` (`data` is a `Depth0` state variable
in `SolcStructs`). -/
def State.solcMemoryStore : State :=
  { storage :=
      [ ("outerX", defaultForRef (RefTy.struct "Outer")),
        ("innerS", defaultForRef (RefTy.struct "Inner")),
        ("inners", SVal.array [] [] false),
        ("prims", SVal.array [] [] false) ] }

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
        ("arrayMap", SVal.map [] (SVal.array [] [] false)),
        ("rows", SVal.array [] [] false),
        ("ledger", defaultForRef (RefTy.struct "Ledger")) ] }

/-- `solc/SolcControlFlow.sol`. -/
def State.solcControlFlowStore : State :=
  { storage :=
      [ ("sx", defaultForRef (RefTy.struct "Pair")),
        ("sy", defaultForRef (RefTy.struct "Pair")),
        ("target", defaultForRef (RefTy.struct "Pair")),
        ("values", SVal.array [] [] false) ] }

end Semantics

/-! ## Running a program -/

open Semantics

variable {C : Contract}

/-- The path an alias is bound to. -/
def aliasPath (σ : State) (x : Var) : Res (Name × List Seg) := do
  match ← σ.getEnv x with
  | .spath root segs => pure (root, segs)
  | .val _ | .mref _ | .store _ | .ledger _ => .error .stuck

/-- A word is stored as it is. -/
@[simp] theorem State.writeStorage_prim (σ : State) (r : Name) (segs : List Seg) (p : PrimVal) :
    σ.writeStorage r segs (.prim p) = σ.saveStorage r segs (.prim p) := rfl

/-- A word is stored as it is: `alice.age = 10;` is a `save`. -/
@[simp] theorem State.writeStorage_toSVal (σ : State) (r : Name) (segs : List Seg) (v : Value) :
    σ.writeStorage r segs v.toSVal = σ.saveStorage r segs v.toSVal := by
  cases v <;> rfl

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

/-- The value a simple value denotes: a literal, a stack local's, or the
environment's. -/
def Simple.eval (σ : State) {p : PrimTy} : Simple C p → Res Value
  | .lit n _ => pure (.int n)
  | .bool b => pure (.bool b)
  | .local x => do
    match ← σ.getEnv x with
    | .val v => pure v
    | .spath .. | .mref _ | .store _ | .ledger _ => .error .stuck
  | .env k _ => pure (.int (σ.envVal k))

/-- The length of the array at a storage path: `values.length`. -/
def arrayLen (σ : State) (r : Name) (segs : List Seg) : Res Value := do
  match ← σ.findStorage r segs with
  | .array elems _ _ => pure (.int elems.length)
  | .prim _ | .struct _ | .map _ _ => .error .stuck

/-- The length of the memory array `id`: `xs.length`. -/
def memArrayLen (σ : State) (id : Nat) : Res Value := do
  match ← σ.getObj id with
  | .array elems _ => pure (.int elems.length)
  | .struct _ => .error .stuck

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
    σ.checkIndex r segs i
    pure (r, segs ++ [.at i])

/-- The slot a memory path holds in `σ`: a memory local's reference, or
what a location holds. -/
def MPath.mval (σ : State) : {T : Ty} → MPath C T → Res MVal
  | _, .var x => do
    match ← σ.getEnv x with
    | .mref id => pure (.ref id)
    | .val _ | .spath .. | .store _ | .ledger _ => .error .stuck
  | _, .loc l => l.read σ

def MLoc.read (σ : State) : {T : Ty} → MLoc C T → Res MVal
  | _, .field b f _ => do
    let id ← (← b.mval σ).asRef
    match ← σ.getObj id with
    | .struct fields =>
      match lookupBy f fields with
      | some v => pure v
      | none => .error .stuck
    | .array _ _ => .error .stuck
  | _, .index _ b i => do
    let id ← (← b.mval σ).asRef
    let iv ← (← i.eval σ).asInt
    match ← σ.getObj id with
    | .array elems _ =>
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
  | _, .len b _ => do
    let (r, segs) ← b.resolve σ
    arrayLen σ r segs
  | _, .mlen b _ => do memArrayLen σ (← (← b.mval σ).asRef)

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
  | .array _ _ => .error .stuck

/-- A write into a memory array's element. -/
def memWriteIndex (σ : State) (id : Nat) (i : Int) (mv : MVal) : Res State := do
  match ← σ.getObj id with
  | .array elems fx =>
    if 0 ≤ i ∧ i.toNat < elems.length then .ok (σ.setObj id (.array (elems.set i.toNat mv) fx))
    else .error .revert
  | .struct _ => .error .stuck

/-- `l = mv` into a memory location. -/
def MLoc.write (σ : State) (mv : MVal) {T : Ty} : MLoc C T → Res State
  | .field b f _ => do
    let id ← (← b.mval σ).asRef
    memWriteField σ id f mv
  | .index _ b i => do
    let id ← (← b.mval σ).asRef
    let iv ← (← i.eval σ).asInt
    memWriteIndex σ id iv mv

/-- The slot a memory source writes: a value, or the object a reference
names.  A reference is read as one (`asRef`), as the calculus's
`write(memory, l, mpath)` reads it: a slot holding a primitive where a
reference is expected is stuck, not copied as it is. -/
def MSrc.mval (σ : State) {T : Ty} : MSrc C T → Res MVal
  | .val v => do pure (← v.eval σ).toMVal
  | .ref p => do pure (.ref (← (← p.mval σ).asRef))

/-- What `new R(n)` allocates, as the storage value it is a copy of: `n`
default elements (a struct element its own fresh object, as solc allocates
one per element). -/
def newArrVal : RefTy → Int → SVal
  | .array E, n => .array (List.replicate n.toNat (defaultForTy E)) [] false
  | R, _ => defaultForRef R

/-- `x` bound to the object a memory right-hand side names: `n`'s by
identity, a fresh deep copy of a storage object, or a fresh array. -/
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
  | .newArr n _ => do
    let sv := newArrVal R (← (← n.eval σ).asInt)
    let (σ', mv) ← copyStToM σ sv
    let id ← mv.asRef
    pure (σ'.setEnv x (.mref id))

/-- A write at a memory address. -/
def writeAddr (σ : State) (mv : MVal) : Addr → Res State
  | .memoryField id f => memWriteField σ id f mv
  | .memoryIndex id i => memWriteIndex σ id i mv

/-- The address of a memory location: the object, and the member or the
index.  An index is checked where it is written (`memWriteIndex`). -/
def MLoc.addr (σ : State) {T : Ty} : MLoc C T → Res Addr
  | .field b f _ => do pure (.memoryField (← (← b.mval σ).asRef) f)
  | .index _ b i => do
    let id ← (← b.mval σ).asRef
    pure (.memoryIndex id (← (← i.eval σ).asInt))

/-- `delete` at a memory address, of a location of type `T`: a primitive is
reset to its default, a reference to a fresh default object (solc; KeY's
`memoryFieldDeleteReference` allocates one). -/
def memClear (σ : State) (a : Addr) : Ty → Res State
  | .prim p => writeAddr σ (PrimTy.default p).toMVal a
  | .ref R => do
    let (σ', id) ← allocDefault σ R
    writeAddr σ' (.ref id) a

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
    | .spath .. | .mref _ | .store _ | .ledger _ => .error .stuck
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
  | p, .mindex _ b i, v => do
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
    | .spath .. | .mref _ | .store _ | .ledger _ => .error .stuck
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
  | p, .mindex _ b i => do
    let id ← (← b.mval σ).asRef
    let iv ← (← i.eval σ).asInt
    bumpMem σ op p (.memoryIndex id iv)

/-- `push` at a resolved array: the element `val` gives (from the slot the
push lands on) appended. -/
def pushAt (σ : State) (E : Ty) (root : Name) (segs : List Seg) (val : SVal → Res SVal) :
    Res State := do
  match ← σ.findStorage root segs with
  | .array elems shadow fx =>
    let (slot, shadow') := pushSlot E shadow
    let newElem ← val slot
    σ.saveStorage root segs (.array (elems ++ [newElem]) shadow' fx)
  | .prim _ | .struct _ | .map _ _ => .error .stuck

/-- `b.push()` as a place: the slot appended, and its index. -/
def pushPlaceAt (σ : State) (E : Ty) (root : Name) (segs : List Seg) : Res (State × Int) := do
  match ← σ.findStorage root segs with
  | .array elems shadow fx =>
    let (slot, shadow') := pushSlot E shadow
    let σ' ← σ.saveStorage root segs (.array (elems ++ [slot]) shadow' fx)
    pure (σ', elems.length)
  | .prim _ | .struct _ | .map _ _ => .error .stuck

/-- What a push appends: the slot, or its argument, laid on fresh slots
(`SVal.strip`: a copy copies the live elements only). -/
def Src.pushVal (σ : State) {T : Ty} : Option (Src C T) → SVal → Res SVal
  | none, slot => pure slot
  | some r, _ => do pure (← r.value σ).strip

/-- `pop` at a resolved array: the last element cleared into the shadow, or
moved there as it is when `keep` (an array of mappings: `delete` leaves a
mapping alone, and solkey's `storagePopSaveMappingElement` writes no
`delAt`). -/
def popAt (σ : State) (keep : Bool) (root : Name) (segs : List Seg) : Res State := do
  match ← σ.findStorage root segs with
  | .array elems shadow fx =>
    match elems.reverse with
    | [] => .error .revert
    | last :: restRev =>
      σ.saveStorage root segs
        (.array restRev.reverse ((if keep then last else last.defaultOf) :: shadow) fx)
  | .prim _ | .struct _ | .map _ _ => .error .stuck

/-- `v` paid by the contract to `a`, on the ledger: `a`'s entry down by `v`,
solkey's `\if(a = self) \then(net) \else(storeSt(net, at(a), selectSt(net, at(a)) - v))`.
A payment to `this` (`address(this)`, `TxEnv.selfAddress`) books nothing: the
contract's own entry is never moved. -/
def Semantics.State.pay (σ : State) (addr amt : Int) : State :=
  { σ with net := if addr = σ.tx.selfAddress then σ.net else setBy addr (σ.getNet addr - amt) σ.net }

/-- A payment as one record update: the ledger alone changes. -/
theorem Semantics.State.pay_eq (σ : State) (addr amt : Int) : σ.pay addr amt =
    { σ with net := if addr = σ.tx.selfAddress then σ.net
      else setBy addr (σ.getNet addr - amt) σ.net } := rfl

/-- `a.transfer(v)` with both evaluated: book the payment on the ledger. -/
def transferAt (σ : State) (addr amt : Int) : Res State :=
  if amt < 0 then .error .stuck
  else .ok (σ.pay addr amt)

/-- The external call a `send` makes: `amt` to `addr` with empty calldata,
which reaches the recipient's `receive` (or fallback) function. -/
def sendKey (addr amt : Int) : ExtKey := ⟨addr, "", [.int amt]⟩

/-- `pv = a.send(v);` with both evaluated: whether the recipient takes the
payment is the transaction's (`TxEnv.ext`, at `sendKey`).  Taken, as the
oracle's `ok` or with no entry (an address with no code accepts), it is
booked as `transfer` books it and `pv` is `true`; refused (any other entry),
nothing is booked and `pv` is `false`: a `send` does not revert.  A
negative amount is stuck, as `transfer`'s. -/
def sendAt (σ : State) (pv : Var) (addr amt : Int) : Res State :=
  if amt < 0 then .error .stuck
  else match lookupBy (sendKey addr amt) σ.tx.ext with
    | none | some (.ok _) => .ok ((σ.pay addr amt).setEnv pv (.val (.bool true)))
    | some _ => .ok (σ.setEnv pv (.val (.bool false)))

/-- An alias bound to what `r` names: a path, or the slot a push appends. -/
def ARhs.bind (σ : State) (x : Var) {R : RefTy} : ARhs C R → Res State
  | .path p => do
    let (root, segs) ← p.resolve σ
    pure (σ.setEnv x (.spath root segs))
  | .push b _ => do
    let (root, segs) ← b.resolve σ
    let (σ', n) ← pushPlaceAt σ (.ref R) root segs
    pure (σ'.setEnv x (.spath root (segs ++ [.at n])))

/-- A call's arguments bound to its parameters, one after another, as its
inlining declares them.  The parameters are fresh at the call and no argument
that is not simple reads one (`Arg.separatedFrom`), so this is solc's
reading of every argument before the callee runs. -/
def Arg.bindSeq : List (Arg C) → State → Res State
  | [], σ => pure σ
  | a :: as, σ => do Arg.bindSeq as (σ.setEnv a.x (.val (← a.e.eval σ)))

/-- Return variables declared at their defaults, one after another. -/
def CallRet.enterAll : List (PrimTy × Var) → State → State
  | [], σ => σ
  | (p, r) :: rs, σ => CallRet.enterAll rs (σ.setEnv r (.val (PrimTy.default p)))

/-- Entering a call: its return variables declared at their defaults, as
solc zeroes them. -/
def CallRet.enter (σ : State) : CallRet → State
  | .none => σ
  | .val p r _ => σ.setEnv r (.val (PrimTy.default p))
  | .rets rs => CallRet.enterAll rs σ

/-- Entering a call binds only its return variables, each to a value: what
holds of two states alike and survives binding a local to a value on both
holds after entering. -/
theorem CallRet.enter_induct₂ {R : State → State → Prop}
    (hset : ∀ σ τ x w, R σ τ → R (σ.setEnv x (.val w)) (τ.setEnv x (.val w))) :
    (ret : CallRet) → {σ τ : State} → R σ τ → R (ret.enter σ) (ret.enter τ)
  | .none, _, _, h => h
  | .val _ _ _, _, _, h => hset _ _ _ _ h
  | .rets rs, _, _, h => go rs h
where
  go : (rs : List (PrimTy × Var)) → {σ τ : State} → R σ τ →
      R (CallRet.enterAll rs σ) (CallRet.enterAll rs τ)
    | [], _, _, h => h
    | (_, _) :: rs, _, _, h => go rs (hset _ _ _ _ h)

/-- `CallRet.enter_induct₂` for one state. -/
theorem CallRet.enter_induct {P : State → Prop} (hset : ∀ τ x w, P τ → P (τ.setEnv x (.val w)))
    (ret : CallRet) {σ : State} (h : P σ) : P (ret.enter σ) :=
  CallRet.enter_induct₂ (R := fun σ _ => P σ) (fun _ _ x w h => hset _ x w h) ret (τ := σ) h

/-- Leaving a call: the returned value assigned where the call is. -/
def CallRet.leave (σ : State) : CallRet → Res State
  | .val p r (some res) => do pure (σ.setEnv res (.val (← (Simple.local r : Simple C p).eval σ)))
  | _ => pure σ

/-- Whether `v` is a value of the type `p`: what decoding a word of returned
data at `p` accepts. -/
def Semantics.PrimVal.fits : Value → PrimTy → Bool
  | .bool _, .bool => true
  | .int n, .uint => decide (0 ≤ n ∧ n < uintBound)
  | .int n, .int => decide (-intBound ≤ n ∧ n < intBound)
  | _, _ => false

/-- The locals an external call's outcome binds, from its data in order, as
the caller decodes it: data too short, or a word that is not a value of its
local's type, reverts (in the caller: no `catch` clause catches it).  Data
past the last local is not read. -/
def bindData : List (PrimTy × Var) → List Value → State → Res State
  | [], _, σ => pure σ
  | (p, x) :: xs, v :: vs, σ =>
    if v.fits p then bindData xs vs (σ.setEnv x (.val v)) else .error .revert
  | _ :: _, [], _ => .error .revert

/-- The call as it is made, its receiver and arguments evaluated. -/
def ExtCall.key (σ : State) (c : ExtCall C) : Res ExtKey := do
  let a ← (← c.addr.eval σ).asInt
  let vs ← c.args.mapM fun a => a.2.eval σ
  pure ⟨a, c.fn, vs⟩

/-- A condition's outcome: `true` goes on, `false` reverts. -/
def guardOk (v : Value) (σ : State) : Res State :=
  match v with
  | .bool true => pure σ
  | .bool false => .error .revert
  | .int _ => .error .stuck

/-- An assertion's outcome: `true` goes on, `false` panics. -/
def assertOk (v : Value) (σ : State) : Res State :=
  match v with
  | .bool true => pure σ
  | .bool false => .error .panic
  | .int _ => .error .stuck

mutual

/-- The state a statement leaves, from `σ`: `alice.age = 10;` saves `10` at
`alice.age`, `Person storage p = alice;` binds `p` to `alice`'s path. -/
def Stmt.run (σ : State) : Stmt C → Res State
  | .assign l r => do
    let sv ← r.value σ
    let (root, segs) ← l.resolve σ
    σ.writeStorage root segs sv
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
    let sv ← copyMem σ (.ref (← (← p.mval σ).asRef))
    let (root, segs) ← l.resolve σ
    σ.writeStorage root segs sv
  | .opAssign op _ _ l r => do l.store σ op (← r.eval σ)
  | .incDec op _ l => do pure (← l.bump σ op).1
  | .assignIncDec x op _ l _ => do
    let (σ', v) ← l.bump σ op
    pure (σ'.setEnv x (.val v))
  | .push (E := E) b v _ => do
    let (root, segs) ← b.resolve σ
    pushAt σ E root segs (Src.pushVal σ v)
  | .pop (E := E) b => do
    let (root, segs) ← b.resolve σ
    popAt σ E.isMapping root segs
  | .transfer r a => do
    let addr ← (← r.eval σ).asInt
    let amt ← (← a.eval σ).asInt
    transferAt σ addr amt
  | .send pv r a => do
    let addr ← (← r.eval σ).asInt
    let amt ← (← a.eval σ).asInt
    sendAt σ pv addr amt
  | .delete l => do
    let (root, segs) ← l.resolve σ
    let cur ← σ.findStorage root segs
    σ.saveStorage root segs cur.defaultOf
  | .deleteMem (T := T) p _ =>
    match p with
    | @MPath.var _ R x => do
      let (σ', id) ← allocDefault σ R
      pure (σ'.setEnv x (.mref id))
    | .loc l => do memClear σ (← l.addr σ) T
  | .assignNew (R := R) l n _ => do
    let sv := newArrVal R (← (← n.eval σ).asInt)
    let (σ', mv) ← copyStToM σ sv
    let id ← mv.asRef
    match l with
    | .store l => do
      let sv' ← copyMem σ' (.ref id)
      let (root, segs) ← l.resolve σ'
      σ'.writeStorage root segs sv'
    | .mem l => l.write σ' (.ref id)
  | .ite c thn els => do
    match ← c.eval σ with
    | .bool true => Prog.run σ thn
    | .bool false => Prog.run σ els
    | .int _ => .error .stuck
  | .require c => do guardOk (← c.eval σ) σ
  | .assert c => do assertOk (← c.eval σ) σ
  | .revert => .error .revert
  | .call _ args _ ret body => do
    let σ₁ ← Arg.bindSeq args σ
    let σ₂ ← Prog.run (ret.enter σ₁) body
    CallRet.leave (C := C) σ₂ ret
  | .tryCall call rets ok err code pnc other => do
    match lookupBy (← call.key σ) σ.tx.ext with
    | none => .error .revert
    | some (.ok vs) => Prog.run (← bindData rets vs σ) ok
    | some .error => Prog.run σ err
    | some (.panic c) => Prog.run (← bindData (codeBinders code) [c] σ) pnc
    | some .other => Prog.run σ other

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

/-- A failing assertion panics. -/
example : (Prog.run State.exampleStore (sol{ assert(age > 3); } : Prog StandardExample)) =
    .error .panic := rfl

/-! The order an `++` inside an expression is captured in is solc's, as
solkey's `TestSuite.sol` pins it: a binary operator's right operand first
(`i++ + i` is `1 + 1`), an assignment's right-hand side before its target
(`a[++i] = ++i` writes `1` at `2`), an index's base before the index
(`matrix[k][k++]` indexes `matrix[0]`). -/

/-- info: (true, true, true) -/
#guard_msgs in
#eval
  ((Prog.run State.testSuiteStore (sol[TestSuite]{ uint i = 1; uint x = i++ + i;
      assert(x == 2); assert(i == 2); })).isOk,
  (Prog.run State.testSuiteStore (sol[TestSuite]{ uint i = 0; values.push(100); values.push(100);
      values.push(100); values[++i] = ++i; assert(values[2] == 1); })).isOk,
  (Prog.run State.testSuiteStore (sol[TestSuite]{ matrix.push(); matrix.push();
      matrix[0].push(0); matrix[1].push(0); uint k = 0; matrix[k][k++] = 77; assert(k == 1);
      assert(matrix[0][0] == 77); assert(matrix[1][0] == 0); })).isOk)

end Examples

end Solidity
