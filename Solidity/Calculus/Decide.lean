import Solidity.Calculus.Close
import Solidity.Calculus.DecideMem
import Solidity.Theory.Bridge.Denote

/-!
# Deciding the storage goals: `sol_decide`

`sol_close` (`Close.lean`) is a tactic: it proves what its `simp` set and
the facts the formula states reach, and a goal it leaves open may be valid.
Two storage keys the formula does not separate are the typical case:
`[ balances[k] = 5; balances[j] = 5; ] balances[k] == 5` is valid, since
either write leaves `5`, but no fact says `k = j` or `k ≠ j`.  A read below
a deleted struct is the other.  This module is mini-solkey's Chapter 15
(`Ch15_Decide`) for the storage fragment: the search replaced by a function,
and a proof that the function loses nothing.

* `Fml.toL` pushes the updates `sol_symex` leaves into the formula
  (mini-solkey's `Fml.applyUpds`).  A term here halts, so a box update's
  term becomes a premise that it returns and a diamond update's a conjunct;
  `Fml.toL_holds` is exact, halts included.
* `LFml.elim` turns every read of a write into a case tree over key
  equalities whose leaves read the initial storage only.  At each write the
  written path and the read one are compared from the root (`cmpSegs`,
  mini-solkey's four cases: equal, above, below, apart).  Each read is
  guarded by what makes it return — the writes under it succeed
  (`LStor.okE`) — and peeled one write at a time (`LStor.readU`, and
  `hasU`/`mapU` for whether a location, or a mapping, is there, `lenU` for
  an array's length: a `delete` empties a dynamic array and keeps a
  fixed-size one's length).
* `Fml.valid_iff_reduce`: `⊨ φ` exactly when `φ.reduce`, the two steps
  composed, holds in every state.  Every step is an equivalence.
* `sol_decide` (`DecideComplete.lean`) rewrites the goal by it, computes the
  reduction, and rewrites once more by `Fml.valid_iff_cons`: the reads of the
  starting storage free, under the constraints a storage puts on them.
  `sol_decide_heuristic`, here, is the finishing step without them.

What the storage adds to mini-solkey's words:

* **Halting.**  A term is a run of the interpreter; the reduction changes the
  order of the runs (a guard, then the read), so two terms are compared by
  what they return (`Sim`), which is all a formula sees.
* **Shapes.**  A read above a write finds a struct, an array or a mapping,
  which is no word; a read below a written word finds nothing.  A write
  succeeds exactly where a read of the same path does, an array's `length`
  aside (`save_ok_iff_find_ok`).
* **`delete`.**  At or below the deleted location, before any key, a read
  finds the default of what was there (`find_defaultOf`): `0` for a `uint`,
  `false` for a `bool`.  Below a key it finds the old entry when the location
  above the key is a mapping, and nothing when it is an array, which
  `delete` empties (`defaultOf_find_at`); the reduction guards such a read by
  a mapping test.

**No well-typed storage is assumed**, and none is needed for the
equivalence: it holds of every state, which is what `⊨` quantifies over.
The price is that a goal true only of well-typed storage is not valid:
`[ delete alice.account; ] alice.account.balance == 0` fails where the old
balance is a `bool` (`Examples/Tactics/Decide.lean`, `deleteWithoutWrite`), while the
same goal after a write of a `uint` is decided.

**Completeness.**  The reduction loses nothing, so `sol_decide` fails on an
invalid formula, as it should.  What it leaves reads a partial tree with
shapes, array bounds and lengths; the constraints between those reads, and
that every choice meeting them is a storage's (mini-solkey's
`LFml.valid_iff`), are `DecideComplete.lean`'s.

**Array bounds.**  The program checks an index where it takes a path
(`State.checkIndex`) and then reads or writes the slot, past the end
included; the target language reads and writes the live storage
(`SVal.findLive`, `SVal.saveLive`), where an index past the end halts.  The
two agree where the path is checked against the storage it reads, which is
what the fragment keeps to (`PTerm.toL_chk`, `live_bridge`).  Binding an
alias returns where its indices are in bounds (`guardPath`); an alias
through an index is checked then and not when used, so a write to the
storage leaves it stale (`SymB.onWrite`) and a later use of it outside the
fragment.

**The fragment** (`Fml.inL`): no modality (run `sol_symex` first) but the
`⟨[ revert(); ]⟩` a branch's cover keeps (`Premise.coverFml`: `true` under
the box, `false` under the diamond), one
element per update, a local, an alias or the storage updated; an equation
as `eqD a b`, both sides defined (a bare `a ≐ b` compares the Theory
values, and a term that halts still denotes one: `Fml.eqDView`), or a bare
`a ≐ b` of a literal (or `msg.sender`) and a literal or a local, where the
two readings agree (`Term.eqLit`: the branch condition `se1 ≐ true` of an
`if`); literals, values of the transaction (`msg.sender`, which no update
changes: `Rel.tx`), locals, operators, conditionals, reads of `storage` and an array's length
(`values.length`, `LStor.lenU`); one write of a value, one `delete`, one
`push` or `pop` (`LStor.arr`), or one copy of a subtree of `storage`
(`alice = bob;`, `LStor.copy`) over `storage` per update; every alias bound by an update
and, through an index, used before the next write to the storage; a storage
variable bound to the storage (`old` of a specification, read as a snapshot:
`LTerm.findP`); a ledger entry or a payment (`transfer`'s), which no term of
the fragment reads; a quantifier over a local the updates before it do not
read (`LFml.all`, a specification's `\forall`).  Outside it: memory (`read`,
`write`, allocation, the copies `copySt`/`copyMem`), a read of the ledger
(`net(a)`).  Of the gaps `Close.lean` lists, this closes the keys the
formula does not separate and the reads below a deleted struct; the memory
defaults and the distinct allocations stay open.

**Arrays and copies** are eliminated as far as the storage before them
says: a read below a pushed array compares its index with the old length
(`arrKey`); a read below a copy reads the source, through its members and
key by key (`copyKeys`, `overlay_findLive_fields`,
`overlay_findLive_nomap`).  The slot a `push()` of a struct or an array
recycles (`pushSlot`) is read where the storage just below says what it
holds (`LStor.slotU`): the element a `pop` of the same array removed,
cleared or kept, or the first element a `delete` of it cleared.  What is
kept whole, as a term over the written storage the closer cannot see into,
is that slot over any other write, and a read below a key of a copy where
the source has a mapping (a mapping met in both keeps the target's
entries).  Such a term is still exact; it only leaves the leaf to the
premises that mention it, or to the closer's typing of reads below a
push (`Facts.slotTy`, `Calculus/Closer.lean`).
-/

namespace Solidity

namespace Decide

open Semantics SemanticsProperties

/-! ## Agreeing on what returns

The terms of this module are evaluated in another order than the program's
(a guard first, then the value), so where both halt they may halt with a
different `Halt`.  No formula can tell: an equation holds when both sides
return, and every other connective passes the halt on.  `Sim` is agreeing on
what returns. -/

/-- Two runs that return the same values: `balances[k]` read directly, or
after checking that `balances[k]` is a location. -/
def Sim {α : Type} (x y : Res α) : Prop := ∀ a, x = .ok a ↔ y = .ok a

/-- A run agrees with itself: `balances[k]` with `balances[k]`. -/
theorem Sim.refl {α : Type} (x : Res α) : Sim x x := fun _ => Iff.rfl

/-- Agreement chains: a guarded read, the read, the read after the writes. -/
theorem Sim.trans {α : Type} {x y z : Res α} (h₁ : Sim x y) (h₂ : Sim y z) : Sim x z :=
  fun a => (h₁ a).trans (h₂ a)

/-- Equal runs agree: `balances[k]` and `balances[k]`. -/
theorem Sim.of_eq {α : Type} {x y : Res α} (h : x = y) : Sim x y := h ▸ Sim.refl x

/-- Two runs that both halt agree. -/
theorem Sim.halt {α : Type} {x y : Res α} (hx : ∀ a, x ≠ .ok a) (hy : ∀ a, y ≠ .ok a) : Sim x y :=
  fun a => ⟨fun h => absurd h (hx a), fun h => absurd h (hy a)⟩

/-- Agreeing steps make agreeing runs. -/
theorem Sim.bind {α β : Type} {x y : Res α} {f g : α → Res β} (hx : Sim x y)
    (hf : ∀ a, Sim (f a) (g a)) : Sim (x >>= f) (y >>= g) := by
  intro b
  simp only [Res.bind_eq_ok]
  constructor
  · rintro ⟨a, h₁, h₂⟩; exact ⟨a, (hx a).1 h₁, (hf a b).1 h₂⟩
  · rintro ⟨a, h₁, h₂⟩; exact ⟨a, (hx a).2 h₁, (hf a b).2 h₂⟩

/-- The segment is a key or an index. -/
def Seg.isAt : Seg → Bool
  | .field _ => false
  | .at _ => true

/-- An operator on agreeing right operands: `a && b` reads `b` only when
`a` is not `false`, and then as the operand does. -/
theorem evalBinop_sim {op : BinOp} {p : PrimTy} {x : Value} {b b' : Res Value} (h : Sim b b') :
    Sim (evalBinop op p x b) (evalBinop op p x b') := by
  unfold evalBinop
  split
  · exact Sim.refl _
  · exact Sim.refl _
  · exact Sim.bind h fun _ => Sim.refl _

/-- `c ? a : b` on agreeing branches. -/
theorem pickBranch_sim {cv : Value} {t t' e e' : Res Value} (ht : Sim t t') (he : Sim e e') :
    Sim (pickBranch cv t e) (pickBranch cv t' e') := by
  cases cv with
  | int _ => exact Sim.refl _
  | bool b => cases b <;> assumption

/-! ## The live storage

A path the program takes is checked at every index against the live length
(`State.checkIndex`), so a read or a write it makes reaches live elements
only, and the slots past an array's end are never read.  The target language
below reads and writes the live storage (`SVal.findLive`, `SVal.saveLive`),
where an index past the end halts: what the program's checked paths and the
slot-level read and write amount to (`live_bridge`). -/

/-- A write through live elements only: an index past the length halts. -/
def _root_.Solidity.Semantics.SVal.saveLive : SVal → List Seg → SVal → Res SVal
  | _, [], new => .ok new
  | .struct fields, .field name :: rest, new =>
      match lookupBy name fields with
      | some old => do
          let updated ← old.saveLive rest new
          .ok (.struct (setBy name updated fields))
      | none => .error .stuck
  | .array elems shadow fx, .at i :: rest, new =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then do
        let updated ← (elems.get ⟨i.toNat, h.2⟩).saveLive rest new
        .ok (.array (elems.set i.toNat updated) shadow fx)
      else .error .revert
  | .map entries dflt, .at i :: rest, new =>
      match lookupBy i entries with
      | some old => do
          let updated ← old.saveLive rest new
          .ok (.map (setBy i updated entries) dflt)
      | none => do
          let updated ← dflt.saveLive rest new
          .ok (.map (setBy i updated entries) dflt)
  | .prim _, _ :: _, _ => .error .stuck
  | .struct _, .at _ :: _, _ => .error .stuck
  | .array _ _ _, .field _ :: _, _ => .error .stuck
  | .map _ _, .field _ :: _, _ => .error .stuck

/-- A live write is read back live: `balances[k] = 5;` then `balances[k]` is `5`. -/
theorem findLive_saveLive_same {old new updated : SVal} {path : List Seg}
    (h : old.saveLive path new = .ok updated) :
    updated.findLive path = .ok new := by
  induction path generalizing old updated with
  | nil =>
      simp only [SVal.saveLive, Except.ok.injEq] at h
      subst updated
      simp only [SVal.findLive_nil]
  | cons seg rest ih =>
      cases seg with
      | field name =>
          cases old <;> try { simp only [SVal.saveLive, reduceCtorEq] at h }
          rename_i fields
          cases hv : lookupBy name fields with
          | none => simp only [SVal.saveLive, hv, reduceCtorEq] at h
          | some old =>
              simp only [SVal.saveLive, hv] at h
              obtain ⟨child, hs, h⟩ := Res.bind_eq_ok.1 h
              cases h
              simp only [SVal.findLive, lookupBy_setBy_self, ih hs]
      | «at» i =>
          cases old <;> try { simp only [SVal.saveLive, reduceCtorEq] at h }
          · rename_i elems shadow fx
            simp only [SVal.saveLive] at h
            split at h
            next hb =>
              obtain ⟨child, hs, h⟩ := Res.bind_eq_ok.1 h
              cases h
              simp only [SVal.findLive, hb, List.length_set, and_self, ↓reduceDIte,
                  List.get_eq_getElem, List.getElem_set_self, ih hs]
            next hb => contradiction
          · rename_i entries dflt
            cases hv : lookupBy i entries with
            | none =>
                simp only [SVal.saveLive, hv] at h
                obtain ⟨child, hs, h⟩ := Res.bind_eq_ok.1 h
                cases h
                simp only [SVal.findLive, lookupBy_setBy_self, ih hs]
            | some old =>
                simp only [SVal.saveLive, hv] at h
                obtain ⟨child, hs, h⟩ := Res.bind_eq_ok.1 h
                cases h
                simp only [SVal.findLive, lookupBy_setBy_self, ih hs]

/-- **Frame, live**: a write leaves every path apart from it as it was. -/
theorem findLive_saveLive_diverge {new : SVal} :
    ∀ {p q : List Seg} {old upd : SVal}, Close.Diverge p q → old.saveLive p new = .ok upd →
      upd.findLive q = old.findLive q
  | [], _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => (Close.not_diverge_nil_right h).elim
  | a :: p, b :: q, old, upd, h, hs => by
    cases old with
    | prim v => cases a <;> simp only [SVal.saveLive, reduceCtorEq] at hs
    | struct fields =>
      cases a with
      | «at» i => simp only [SVal.saveLive, reduceCtorEq] at hs
      | field n =>
        simp only [SVal.saveLive] at hs
        split at hs
        · rename_i old' hl
          obtain ⟨u, hu, hs⟩ := Res.bind_eq_ok.1 hs
          cases hs
          cases b with
          | «at» j => simp only [SVal.findLive]
          | field m =>
            by_cases hnm : m = n
            · subst hnm
              have hd : Close.Diverge p q := by simpa only [Close.diverge_cons, ne_eq,
                  not_true_eq_false, false_or] using h
              simp only [SVal.findLive, lookupBy_setBy_self, findLive_saveLive_diverge hd hu, hl]
            · simp only [SVal.findLive, lookupBy_setBy_ne hnm]
        · simp only [reduceCtorEq] at hs
    | array elems shadow fx =>
      cases a with
      | field n => simp only [SVal.saveLive, reduceCtorEq] at hs
      | «at» i =>
        simp only [SVal.saveLive] at hs
        split at hs
        · rename_i hi
          obtain ⟨u, hu, hs⟩ := Res.bind_eq_ok.1 hs
          simp only [List.get_eq_getElem] at hu
          cases hs
          cases b with
          | field m =>
            -- `length` reads the extent, which a write in bounds keeps
            by_cases hm : m = "length"
            · subst hm; cases fx <;> simp only [SVal.findLive, Bool.false_eq_true, ↓reduceIte,
                List.length_set]
            · simp only [SVal.findLive]
          | «at» j =>
            by_cases hij : j = i
            · subst hij
              have hd : Close.Diverge p q := by simpa only [Close.diverge_cons, ne_eq,
                  not_true_eq_false, false_or] using h
              simp only [SVal.findLive, hi, List.length_set, and_self, ↓reduceDIte,
                  List.get_eq_getElem, List.getElem_set_self, findLive_saveLive_diverge hd hu]
            · by_cases hj : 0 ≤ j ∧ j.toNat < elems.length
              · have hne : i.toNat ≠ j.toNat := by omega
                simp only [SVal.findLive, hj, List.length_set, and_self, ↓reduceDIte,
                    List.get_eq_getElem, List.getElem_set_ne hne]
              · simp only [SVal.findLive, List.length_set, hj, ↓reduceDIte]
        · simp only [reduceCtorEq] at hs
    | map entries dflt =>
      cases a with
      | field n => simp only [SVal.saveLive, reduceCtorEq] at hs
      | «at» i =>
        simp only [SVal.saveLive] at hs
        -- the slot written: the entry at `i`, or the default when there is none
        obtain ⟨old', hold, hfind⟩ : ∃ old' : SVal, (old'.saveLive p new >>= fun u =>
            Except.ok (SVal.map (setBy i u entries) dflt)) = Except.ok upd ∧
            (SVal.map entries dflt).findLive (.at i :: q) = old'.findLive q := by
          split at hs <;> rename_i hl <;> exact ⟨_, hs, by simp only [SVal.findLive, hl]⟩
        obtain ⟨u, hu, hold⟩ := Res.bind_eq_ok.1 hold
        cases hold
        cases b with
        | field m => simp only [SVal.findLive]
        | «at» j =>
          by_cases hij : j = i
          · subst hij
            have hd : Close.Diverge p q := by simpa only [Close.diverge_cons, ne_eq,
                not_true_eq_false, false_or] using h
            simp only [SVal.findLive, lookupBy_setBy_self] at hfind ⊢
            rw [hfind, findLive_saveLive_diverge hd hu]
          · simp only [SVal.findLive, lookupBy_setBy_ne hij]

/-! ## The target language

A term here is read in the state the formula *starts* in: every update has
been pushed into it.  A storage is a stack of writes over that state's
storage (`LStor`), and the storage as a whole is one tree, the struct of its
roots (`SVal.struct σ.storage`), so that a root is the first segment of a
path and a write at a root is a write like any other.

A memory is written as solkey writes it (`LMem`): the initial heap, and
the allocations and writes on top of it, run with the interpreter's own
operations (`LMem.run`).  Its objects are named by the allocation that made
them and a literal path (`LId`, KeY's `idC(freshIdp, flds)`), never by the
interpreter's numbers, so two names are compared statically.  A memory
object copied back is a storage of one root (`LStor.view`), which the
storage overlay reads as any other. -/

/-- A shape the location above a key is tested for, below a `delete`: a
mapping keeps its entries (`delete` leaves it alone), a fixed-size array keeps
its elements' places (`delete` resets them in place). -/
inductive KShape where
  | map
  | fixed
  deriving Inhabited, Repr, DecidableEq, Lean.ToExpr

deriving instance Lean.ToExpr for EnvKey
deriving instance Lean.ToExpr for PrimTy
deriving instance Lean.ToExpr for Seg

/-- A memory object named as solkey names it, `idC(freshIdp, flds)`: the
`root`-th allocation of the leaf (KeY's `freshIdp`, counted from `0`) and the
literal selectors from it.  Names are compared statically, roots first; a
name denotes the object it resolves to in the heap of its birth
(`Calculus/MemNames.lean`, `Births.eval`), so a later reference write is seen
through the slot it writes, never by renaming. -/
structure LId where
  root : Nat
  path : List Seg
  deriving Inhabited, Repr, DecidableEq, Lean.ToExpr

/-- The root a view of memory as storage (`LStor.view`) puts its object at:
the view is the one-root tree `{viewRoot ↦ copyMem(m, i)}`, so the storage
overlay (`LStor.copy`) reads it as it reads a storage root. -/
def viewRoot : Name := "#view"

/-- The state a memory run starts from: the initial one, its locals
dropped, since no memory operation reads them; binding a local leaves it
alone (`memBase_setEnv`). -/
def memBase (σ : State) : State := { σ with env := [] }

theorem memBase_setEnv (σ : State) (x : Var) (b : Binding) :
    memBase (σ.setEnv x b) = memBase σ := rfl

/-- What an operation does to the array at a path: `values.push(w)` appends
the word and consumes the first slot past the end, `persons.push()` appends
the slot `pushSlot E` gives (recycled, or a default), `values.pop()` moves
the last element into the slots past the end, cleared (`keep`: as it is, an
array of mappings').  The interpreter's `pushOn` and `popOn`, on the node
alone. -/
inductive AOp where
  | push
  | slot (E : Ty)
  | pop (keep : Bool)
  deriving Inhabited, Repr, DecidableEq, Lean.ToExpr

/-- The array node after the operation; a word `w` for a push. -/
def AOp.apply : AOp → Value → SVal → Res SVal
  | .push, w, .array elems shadow fx =>
    .ok (.array (elems ++ [w.toSVal]) (pushSlot .uint shadow).2 fx)
  | .slot E, _, .array elems shadow fx =>
    .ok (.array (elems ++ [(pushSlot E shadow).1]) (pushSlot E shadow).2 fx)
  | .pop keep, _, .array elems shadow fx =>
    match elems.reverse with
    | [] => .error .revert
    | last :: restRev =>
      .ok (.array restRev.reverse ((if keep then last else last.defaultOf) :: shadow) fx)
  | _, _, .prim _ | _, _, .struct _ | _, _, .map _ _ => .error .stuck

mutual

/-- A value, read in the initial state. -/
inductive LTerm where
  | lit (v : Value)
  | var (x : Var)
  | binop (op : BinOp) (p : PrimTy) (a b : LTerm)
  | unop (op : UnOp) (p : PrimTy) (a : LTerm)
  | ite (c a b : LTerm)
  /-- The word at `q` in the storage `s`. -/
  | find (s : LStor) (q : LPath)
  /-- `true` when `q` names a location of `s`, of any shape. -/
  | has (s : LStor) (q : LPath)
  /-- `true` when `q` names a mapping (a fixed-size array) of `s`. -/
  | kmap (sh : KShape) (s : LStor) (q : LPath)
  /-- The length of the array at `q` in `s`: `values.length`. -/
  | len (s : LStor) (q : LPath)
  /-- `true` when the writes of `s` all succeed. -/
  | sok (s : LStor)
  /-- `true` when the keys of `q` are integers. -/
  | pok (q : LPath)
  /-- `d`, then `a`: `a` guarded by `d` returning. -/
  | seq (d a : LTerm)
  /-- `a`, or `b` where `a` halts. -/
  | orElse (a b : LTerm)
  /-- `t` when the keys `a` and `b` are the same integer, `e` when they are
  different ones; it halts when either is no integer. -/
  | kite (a b t e : LTerm)
  /-- The default of the word `a` returns: `0` or `false`. -/
  | zero (a : LTerm)
  | err
  /-- A value of the transaction: `msg.sender`.  No update changes it. -/
  | env (k : EnvKey)
  /-- The word at `q` in the storage `s`, read as a snapshot is: past the
  live length too (`SVal.find`), its path checked elsewhere.  `\old(e)` of a
  specification reads `old` so. -/
  | findP (s : LStor) (q : LPath)
  /-- `true` when the subtree at `q` of `s` copies into memory: it holds no
  mapping (`copyStToM`), as the program's `copySt` asks. -/
  | cpok (s : LStor) (q : LPath)
  deriving Inhabited, Repr, Lean.ToExpr

/-- A storage path, the root first; built from the right as `PTerm` is. -/
inductive LPath where
  | root (r : Name)
  | field (q : LPath) (f : Name)
  | at (q : LPath) (k : LTerm)
  deriving Inhabited, Repr, Lean.ToExpr

/-- A storage: the initial one, and the writes on top of it. -/
inductive LStor where
  | init
  | save (s : LStor) (q : LPath) (w : LTerm)
  | del (s : LStor) (q : LPath)
  /-- The operation `op` on the array at `q`, with the word `w` for a push
  (a literal otherwise). -/
  | arr (op : AOp) (s : LStor) (q : LPath) (w : LTerm)
  /-- The subtree at `sq` of the storage `src` copied over `q` (`alice = bob;`,
  `SVal.overlay`). -/
  | copy (s : LStor) (q : LPath) (src : LStor) (sq : LPath)
  /-- The object `i` of the memory `m` copied back, as the one-root storage
  `{viewRoot ↦ copyMem(mtSt, m, i)}`. -/
  | view (m : LMem) (i : LId)
  deriving Inhabited, Repr, Lean.ToExpr

/-- A memory, as solkey writes one: the initial memory, and the
allocations and writes on top of it.  The `k` of an allocation is its
ordinal among the leaf's allocations, KeY's `freshIdp`. -/
inductive LMem where
  | init
  /-- `addM(m)`: a default `R` allocated. -/
  | addM (m : LMem) (k : Nat) (R : RefTy)
  /-- `new R(n)` allocated, its elements defaults: KeY's `addM` and the
  write of its `size`, one node here. -/
  | newArr (m : LMem) (k : Nat) (R : RefTy) (n : LTerm)
  /-- `copySt(m, find(s, q))`: the subtree at `q` of `s` copied in. -/
  | copySt (m : LMem) (k : Nat) (s : LStor) (q : LPath)
  /-- `write(m, i, a, v)`. -/
  | write (m : LMem) (i : LId) (a : LSel) (v : LMV)
  deriving Inhabited, Repr, Lean.ToExpr

/-- What selects in a memory object: a member, an element, or the length
(KeY's `size`, which only a read selects here). -/
inductive LSel where
  | fld (f : Name)
  | idx (t : LTerm)
  | size
  deriving Inhabited, Repr, Lean.ToExpr

/-- What a memory slot holds: a word, or a reference to a named object. -/
inductive LMV where
  | word (t : LTerm)
  | ref (i : LId)
  deriving Inhabited, Repr, Lean.ToExpr

end

deriving instance DecidableEq for LTerm, LPath, LStor, LMem, LSel, LMV

/-- A first-order formula over those terms. -/
inductive LFml where
  | tt
  | eq (a b : LTerm)
  | not (φ : LFml)
  | and (φ ψ : LFml)
  | imp (φ ψ : LFml)
  /-- For every value of the type, `x` holding it: a quantifier of a
  specification, `\forall address a`. -/
  | all (x : Var) (p : PrimTy) (φ : LFml)
  deriving Inhabited, Repr, Lean.ToExpr

/-- Two keys are the same integer: `k == j` in `balances[k]` against
`balances[j]`.  A key that is not one is equal to nothing. -/
def keyEq : Res Int → Res Int → Bool
  | .ok i, .ok j => decide (i = j)
  | _, _ => false

/-- The value is a mapping. -/
def isMapV : SVal → Bool
  | .map _ _ => true
  | _ => false

/-- A mapping returns `true`, anything else halts. -/
def kmapF (n : SVal) : Res Value := if isMapV n then .ok (.bool true) else .error .stuck

/-- The value is a fixed-size array (marked, `SVal.array`'s `fixed`). -/
def isFixV : SVal → Bool
  | .array _ _ fx => fx
  | _ => false

/-- A value of the shape returns `true`, anything else halts. -/
def KShape.test : KShape → SVal → Res Value
  | .map, n => kmapF n
  | .fixed, n => if isFixV n then .ok (.bool true) else .error .stuck

/-- `a`'s value, or `b`'s where `a` halts. -/
def orElseR (a b : Res Value) : Res Value :=
  match a with
  | .ok v => .ok v
  | .error _ => b

@[simp] theorem orElseR_ok (v : Value) (b : Res Value) : orElseR (.ok v) b = .ok v := rfl
@[simp] theorem orElseR_error (e : Halt) (b : Res Value) : orElseR (.error e) b = b := rfl

/-- The default of a word: `delete x;` leaves `0` in a `uint`, `false` in a
`bool`. -/
def zeroV : Value → Value
  | .int _ => .int 0
  | .bool _ => .bool false

/-- The object a name denotes, in the births `B`; it halts on a name of no
object. -/
def LId.evalR (B : MemNames.Births) (i : LId) : Res Nat :=
  match B.eval i.root i.path with
  | some n => .ok n
  | none => .error .stuck

mutual

/-- What a term returns in the initial state `σ`: `find(save(init, balances[k], 5),
balances[k])` returns `5` where `balances[k]` is a location. -/
def LTerm.eval (σ : State) : LTerm → Res Value
  | .lit v => .ok v
  | .var x => σ.getEnv x >>= Close.bindingVal
  | .binop op p a b => a.eval σ >>= fun x => evalBinop op p x (b.eval σ)
  | .unop op p a => a.eval σ >>= fun x => applyUnOp op x >>= unopCheck op p
  | .ite c a b => c.eval σ >>= fun cv => pickBranch cv (a.eval σ) (b.eval σ)
  | .find s q => s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= SVal.asValue
  | .has s q => s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= fun _ => .ok (.bool true)
  | .kmap sh s q => s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= sh.test
  | .len s q => s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= Close.arrLen
  | .sok s => s.eval σ >>= fun _ => .ok (.bool true)
  | .pok q => q.eval σ >>= fun _ => .ok (.bool true)
  | .seq d a => d.eval σ >>= fun _ => a.eval σ
  | .orElse a b => orElseR (a.eval σ) (b.eval σ)
  | .kite a b t e =>
    (a.eval σ >>= Value.asInt) >>= fun i => (b.eval σ >>= Value.asInt) >>= fun j =>
      if i = j then t.eval σ else e.eval σ
  | .zero a => a.eval σ >>= fun v => .ok (zeroV v)
  | .err => .error .stuck
  | .env k => .ok (.int (σ.envVal k))
  | .findP s q => s.eval σ >>= fun v => q.eval σ >>= fun qs => v.find qs >>= SVal.asValue
  | .cpok s q => s.eval σ >>= fun v => q.eval σ >>= fun qs => v.find qs >>= fun sv =>
      copyStToM (memBase σ) sv >>= fun _ => .ok (.bool true)

/-- The path a term names, root first: `balances[k]` is `[balances, at k]`. -/
def LPath.eval (σ : State) : LPath → Res (List Seg)
  | .root r => .ok [.field r]
  | .field q f => q.eval σ >>= fun qs => .ok (qs ++ [.field f])
  | .at q k => q.eval σ >>= fun qs => k.eval σ >>= Value.asInt >>= fun i => .ok (qs ++ [.at i])

/-- The storage the writes leave, as one tree: `save(init, balances[k], 5)` is
the tree of `σ` after `balances[k] = 5;`. -/
def LStor.eval (σ : State) : LStor → Res SVal
  | .init => .ok (.struct σ.storage)
  | .save s q w => w.eval σ >>= fun wv => s.eval σ >>= fun v => q.eval σ >>= fun qs =>
      v.saveLive qs wv.toSVal
  | .del s q => s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= fun cur =>
      v.saveLive qs cur.defaultOf
  | .arr op s q w => w.eval σ >>= fun wv => s.eval σ >>= fun v => q.eval σ >>= fun qs =>
      v.findLive qs >>= fun c => op.apply wv c >>= fun c' => v.saveLive qs c'
  | .copy s q src sq => src.eval σ >>= fun sv => sq.eval σ >>= fun sqs => sv.findLive sqs >>=
      fun n => s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= fun cur =>
        v.saveLive qs (cur.overlay n)
  | .view m i => m.run σ >>= fun r => LId.evalR r.2 i >>= fun n =>
      copyMem r.1 (.ref n) >>= fun v => .ok (.struct [(viewRoot, v)])

/-- The memory `m` leaves, run from `σ`'s with the interpreter's own
operations, and its allocations in order (`MemNames.Births`).  An
allocation's ordinal is checked against the allocations before it. -/
def LMem.run (σ : State) : LMem → Res (State × MemNames.Births)
  | .init => .ok (memBase σ, [])
  | .addM m k R => m.run σ >>= fun r =>
      if k = r.2.length then
        allocDefault r.1 R >>= fun a => .ok (a.1, r.2 ++ [MemNames.Birth.ofCopy r.1 a.1 a.2])
      else .error .stuck
  | .newArr m k R n => n.eval σ >>= Value.asInt >>= fun c => m.run σ >>= fun r =>
      if k = r.2.length then
        copyStToM r.1 (newArrVal R c) >>= fun a => a.2.asRef >>= fun id =>
          .ok (a.1, r.2 ++ [MemNames.Birth.ofCopy r.1 a.1 id])
      else .error .stuck
  | .copySt m k s q => s.eval σ >>= fun v => q.eval σ >>= fun qs => v.find qs >>= fun sv =>
      m.run σ >>= fun r =>
      if k = r.2.length then
        copyStToM r.1 sv >>= fun a => a.2.asRef >>= fun id =>
          .ok (a.1, r.2 ++ [MemNames.Birth.ofCopy r.1 a.1 id])
      else .error .stuck
  | .write m i a v => m.run σ >>= fun r => LId.evalR r.2 i >>= fun n => a.addr σ n >>= fun ad =>
      v.eval σ r.2 >>= fun mv => writeAddr r.1 mv ad >>= fun μ => .ok (μ, r.2)

/-- The address `a` selects in the object `n`; the length is no slot. -/
def LSel.addr (σ : State) (n : Nat) : LSel → Res Addr
  | .fld f => .ok (.memoryField n f)
  | .idx t => t.eval σ >>= Value.asInt >>= fun j => .ok (.memoryIndex n j)
  | .size => .error .stuck

/-- The slot a memory value fills, its names read in the births `B`. -/
def LMV.eval (σ : State) (B : MemNames.Births) : LMV → Res MVal
  | .word t => t.eval σ >>= fun v => .ok v.toMVal
  | .ref i => LId.evalR B i >>= fun n => .ok (.ref n)

end

mutual

/-- The free locals of a term: those the initial state is asked for. -/
def LTerm.vars : LTerm → List Var
  | .lit _ | .err | .env _ => []
  | .var x => [x]
  | .binop _ _ a b | .seq a b => a.vars ++ b.vars
  | .unop _ _ a | .zero a => a.vars
  | .orElse a b => a.vars ++ b.vars
  | .ite c a b => c.vars ++ a.vars ++ b.vars
  | .find s q | .has s q | .kmap _ s q | .len s q | .findP s q | .cpok s q => s.vars ++ q.vars
  | .sok s => s.vars
  | .pok q => q.vars
  | .kite a b t e => a.vars ++ b.vars ++ t.vars ++ e.vars

/-- The free locals of a path: the `k` of `balances[k]`. -/
def LPath.vars : LPath → List Var
  | .root _ => []
  | .field q _ => q.vars
  | .at q k => q.vars ++ k.vars

/-- The free locals of a storage: the `k` of `save(init, balances[k], 5)`. -/
def LStor.vars : LStor → List Var
  | .init => []
  | .save s q w => s.vars ++ q.vars ++ w.vars
  | .del s q => s.vars ++ q.vars
  | .arr _ s q w => s.vars ++ q.vars ++ w.vars
  | .copy s q src sq => s.vars ++ q.vars ++ src.vars ++ sq.vars
  | .view m _ => m.vars

/-- The free locals of a memory: the `i` of `write(m, xs, at(i), 1)`. -/
def LMem.vars : LMem → List Var
  | .init => []
  | .addM m _ _ => m.vars
  | .newArr m _ _ n => m.vars ++ n.vars
  | .copySt m _ s q => m.vars ++ s.vars ++ q.vars
  | .write m _ a v => m.vars ++ a.vars ++ v.vars

/-- The free locals of a selector. -/
def LSel.vars : LSel → List Var
  | .fld _ | .size => []
  | .idx t => t.vars

/-- The free locals of a memory value. -/
def LMV.vars : LMV → List Var
  | .word t => t.vars
  | .ref _ => []

end


/-- Rebinding a local the term does not mention leaves what it returns:
`balances[k]` is read alike whatever `a` holds. -/
theorem State.envVal_setEnv (σ : State) (x : Var) (b : Binding) (k : EnvKey) :
    (σ.setEnv x b).envVal k = σ.envVal k := by
  cases k <;> rfl

mutual

theorem LTerm.eval_setEnv {σ : State} {x : Var} {b : Binding} :
    (t : LTerm) → x ∉ t.vars → t.eval (σ.setEnv x b) = t.eval σ
  | .lit _, _ | .err, _ => rfl
  | .env k, _ => by simp only [LTerm.eval, State.envVal_setEnv]
  | .var y, h => by
    have hy : y ≠ x := fun e => h (by simp only [LTerm.vars, e, List.mem_cons, List.not_mem_nil,
        or_false])
    simp only [LTerm.eval, State.getEnv_setEnv_ne hy]
  | .binop _ _ a b', h | .seq a b', h | .orElse a b', h => by
    simp only [LTerm.vars, List.mem_append, not_or] at h
    simp only [LTerm.eval, LTerm.eval_setEnv a h.1, LTerm.eval_setEnv b' h.2]
  | .unop _ _ a, h | .zero a, h => by
    simp only [LTerm.vars] at h
    simp only [LTerm.eval, LTerm.eval_setEnv a h]
  | .ite c a b', h => by
    simp only [LTerm.vars, List.mem_append, not_or] at h
    simp only [LTerm.eval, LTerm.eval_setEnv c h.1.1, LTerm.eval_setEnv a h.1.2,
      LTerm.eval_setEnv b' h.2]
  | .find s q, h | .has s q, h | .kmap _ s q, h | .len s q, h | .findP s q, h => by
    simp only [LTerm.vars, List.mem_append, not_or] at h
    simp only [LTerm.eval, LStor.eval_setEnv s h.1, LPath.eval_setEnv q h.2]
  | .cpok s q, h => by
    simp only [LTerm.vars, List.mem_append, not_or] at h
    simp only [LTerm.eval, LStor.eval_setEnv s h.1, LPath.eval_setEnv q h.2, memBase_setEnv]
  | .sok s, h => by
    simp only [LTerm.vars] at h
    simp only [LTerm.eval, LStor.eval_setEnv s h]
  | .pok q, h => by
    simp only [LTerm.vars] at h
    simp only [LTerm.eval, LPath.eval_setEnv q h]
  | .kite a b' t e, h => by
    simp only [LTerm.vars, List.mem_append, not_or] at h
    simp only [LTerm.eval, LTerm.eval_setEnv a h.1.1.1, LTerm.eval_setEnv b' h.1.1.2,
      LTerm.eval_setEnv t h.1.2, LTerm.eval_setEnv e h.2]

theorem LPath.eval_setEnv {σ : State} {x : Var} {b : Binding} :
    (q : LPath) → x ∉ q.vars → q.eval (σ.setEnv x b) = q.eval σ
  | .root _, _ => rfl
  | .field q _, h => by
    simp only [LPath.vars] at h
    simp only [LPath.eval, LPath.eval_setEnv q h]
  | .at q k, h => by
    simp only [LPath.vars, List.mem_append, not_or] at h
    simp only [LPath.eval, LPath.eval_setEnv q h.1, LTerm.eval_setEnv k h.2]

theorem LStor.eval_setEnv {σ : State} {x : Var} {b : Binding} :
    (s : LStor) → x ∉ s.vars → s.eval (σ.setEnv x b) = s.eval σ
  | .init, _ => rfl
  | .save s q w, h => by
    simp only [LStor.vars, List.mem_append, not_or] at h
    simp only [LStor.eval, LStor.eval_setEnv s h.1.1, LPath.eval_setEnv q h.1.2,
      LTerm.eval_setEnv w h.2]
  | .del s q, h => by
    simp only [LStor.vars, List.mem_append, not_or] at h
    simp only [LStor.eval, LStor.eval_setEnv s h.1, LPath.eval_setEnv q h.2]
  | .arr _ s q w, h => by
    simp only [LStor.vars, List.mem_append, not_or] at h
    simp only [LStor.eval, LStor.eval_setEnv s h.1.1, LPath.eval_setEnv q h.1.2,
      LTerm.eval_setEnv w h.2]
  | .copy s q src sq, h => by
    simp only [LStor.vars, List.mem_append, not_or] at h
    simp only [LStor.eval, LStor.eval_setEnv s h.1.1.1, LPath.eval_setEnv q h.1.1.2,
      LStor.eval_setEnv src h.1.2, LPath.eval_setEnv sq h.2]
  | .view m _, h => by
    simp only [LStor.vars] at h
    simp only [LStor.eval, LMem.run_setEnv m h]

theorem LMem.run_setEnv {σ : State} {x : Var} {b : Binding} :
    (m : LMem) → x ∉ m.vars → m.run (σ.setEnv x b) = m.run σ
  | .init, _ => by simp only [LMem.run, memBase_setEnv]
  | .addM m _ _, h => by
    simp only [LMem.vars] at h
    simp only [LMem.run, LMem.run_setEnv m h]
  | .newArr m _ _ n, h => by
    simp only [LMem.vars, List.mem_append, not_or] at h
    simp only [LMem.run, LMem.run_setEnv m h.1, LTerm.eval_setEnv n h.2]
  | .copySt m _ s q, h => by
    simp only [LMem.vars, List.mem_append, not_or] at h
    simp only [LMem.run, LMem.run_setEnv m h.1.1, LStor.eval_setEnv s h.1.2,
      LPath.eval_setEnv q h.2]
  | .write m _ a v, h => by
    simp only [LMem.vars, List.mem_append, not_or] at h
    simp only [LMem.run, LMem.run_setEnv m h.1.1, LSel.addr_setEnv a h.1.2, LMV.eval_setEnv v h.2]

theorem LSel.addr_setEnv {σ : State} {x : Var} {b : Binding} {n : Nat} :
    (a : LSel) → x ∉ a.vars → a.addr (σ.setEnv x b) n = a.addr σ n
  | .fld _, _ | .size, _ => rfl
  | .idx t, h => by
    simp only [LSel.vars] at h
    simp only [LSel.addr, LTerm.eval_setEnv t h]

theorem LMV.eval_setEnv {σ : State} {x : Var} {b : Binding} {B : MemNames.Births} :
    (v : LMV) → x ∉ v.vars → v.eval (σ.setEnv x b) B = v.eval σ B
  | .word t, h => by
    simp only [LMV.vars] at h
    simp only [LMV.eval, LTerm.eval_setEnv t h]
  | .ref _, _ => rfl

end

/-- A formula holds when, as in `holds` of `eqD`, both sides of each equation
return and agree. -/
def LFml.holds (σ : State) : LFml → Prop
  | .tt => True
  | .eq a b =>
    match a.eval σ, b.eval σ with
    | .ok x, .ok y => x = y
    | _, _ => False
  | .not φ => ¬ φ.holds σ
  | .and φ ψ => φ.holds σ ∧ ψ.holds σ
  | .imp φ ψ => φ.holds σ → ψ.holds σ
  | .all x p φ => ∀ v, p.admits v → φ.holds (σ.setEnv x (.val v))

/-! ## Memory, read off the objects the updates allocated

The objects the updates allocate are kept as `SObj`s over the terms of this
language (`Calculus/DecideMem.lean`): a read is the term its slot holds, an
index into an array a case split on the index (`kchainL`) where it is not a
literal, and each guard returns exactly where the interpreter's operation
does. -/

/-- The value a term has in every state, built from literals by operators
that return on them: the `1` of `xs[0 + 1]`. -/
def LTerm.ground? : LTerm → Option Value
  | .lit v => some v
  | .binop op p a b =>
    match a.ground?, b.ground? with
    | some x, some y =>
      match evalBinop op p x (.ok y) with
      | .ok r => some r
      | .error _ => none
    | _, _ => none
  | .unop op p a =>
    match a.ground? with
    | some x =>
      match applyUnOp op x >>= unopCheck op p with
      | .ok r => some r
      | .error _ => none
    | none => none
  | _ => none

/-- `a`, guarded by `g` returning; `a` alone after a literal. -/
def seqL (g a : LTerm) : LTerm :=
  match g with
  | .lit _ => a
  | g => .seq g a

/-- What returns exactly where `t` returns an integer: the index of `xs[t]`. -/
def isIntL (t : LTerm) : LTerm :=
  match t.ground? with
  | some (.int _) => .lit (.bool true)
  | _ => .kite t t (.lit (.bool true)) (.lit (.bool true))

/-- The word a slot holds; a reference is no word. -/
def slotT : SMV LTerm → LTerm
  | .val t => t
  | .ref _ => .err

/-- The element at the index `t` of the slots `es`, the first at `j`; it
halts past them. -/
def kchainL (t : LTerm) : Nat → List (SMV LTerm) → LTerm
  | _, [] => .err
  | j, e :: es => .kite t (.lit (.int j)) (slotT e) (kchainL t (j + 1) es)

/-- What selects in a memory object: a member, or an index term. -/
inductive MSel where
  | fld (f : Name)
  | idx (t : LTerm)
  deriving Inhabited

/-- A slot holds a word. -/
def SMV.isVal : SMV LTerm → Bool
  | .val _ => true
  | .ref _ => false

/-- The read `read(memory, a)`: the word at the member or the index of the
`k`-th object; none where there is no such object. -/
def readL (M : SMem LTerm) (k : Nat) (sel : MSel) : Option LTerm :=
  match M[k]?, sel with
  | some (.struct fs), .fld f =>
    some (match lookupBy f fs with
      | some e => slotT e
      | none => .err)
  | some (.array es _), .idx t =>
    some (match t.ground? with
      | some (.int i) => if h : 0 ≤ i ∧ i.toNat < es.length then slotT es[i.toNat] else .err
      | _ => kchainL t 0 es)
  | some _, _ => some .err
  | none, _ => none

/-- The length of the `k`-th object, `xs.length`. -/
def mlenL (M : SMem LTerm) (k : Nat) : Option LTerm :=
  match M[k]? with
  | some (.array es _) => some (.lit (.int es.length))
  | some (.struct _) => some .err
  | none => none

/-- The object a reference slot names: `carol.account`, `toks[0]` at a
literal index. -/
def ireadL (M : SMem LTerm) (k : Nat) (sel : MSel) : Option Nat :=
  match M[k]?, sel with
  | some (.struct fs), .fld f =>
    match lookupBy f fs with
    | some (.ref k') => some k'
    | _ => none
  | some (.array es _), .idx t =>
    match t.ground? with
    | some (.int i) =>
      if h : 0 ≤ i ∧ i.toNat < es.length then
        match es[i.toNat] with
        | .ref k' => some k'
        | .val _ => none
      else none
    | _ => none
  | _, _ => none

/-- The elements after a word `u` written at the index `t`, which is no
literal: each is `u` where `t` is its index. -/
def kwriteL (t u : LTerm) (es : List (SMV LTerm)) : List (SMV LTerm) :=
  es.mapIdx fun j e => .val (.kite t (.lit (.int j)) u (slotT e))

/-- The write `write(memory, a, s)`: the objects after it, and what returns
exactly where it does (an index in range); none where the object is not
there, or a reference is written at an index that is no literal. -/
def writeL (M : SMem LTerm) (k : Nat) (sel : MSel) (s : SMV LTerm) :
    Option (SMem LTerm × LTerm) :=
  match M[k]?, sel with
  | some (.struct fs), .fld f => some (M.set k (.struct (setBy f s fs)), .lit (.bool true))
  | some (.array es fx), .idx t =>
    match t.ground? with
    | some (.int i) =>
      if 0 ≤ i ∧ i.toNat < es.length then
        some (M.set k (.array (es.set i.toNat s) fx), .lit (.bool true))
      else some (M, .err)
    | _ =>
      match s with
      | .val u =>
        if es.all SMV.isVal then
          some (M.set k (.array (kwriteL t u es) fx),
            kchainL t 0 (es.map fun _ => .val (.lit (.bool true))))
        else none
      | .ref _ => none
  | some _, _ => some (M, .err)
  | none, _ => none

/-! ## Pushing the updates in

`sol_symex` leaves `{U₁} … {Uₙ} φ`.  Each update is pushed into what follows
it: a local becomes the term it was bound to, an alias the path, `storage`
the stack of writes.  Under the box the update's own term becomes a
premise, under the diamond a conjunct: a run that halts proves every box
formula and no diamond one, and `eq t t` says exactly that `t` returns.
This is mini-solkey's `Fml.applyUpds` (Chapter 14), and here it is exact,
halts included. -/

/-- What an update bound a name to. -/
inductive SymB where
  | val (t : LTerm)
  | path (q : LPath)
  /-- An alias through an index, bound before the storage last changed: it
  was checked against a storage that is gone, and is outside the fragment. -/
  | stale
  /-- A storage variable bound to a storage: `old` of `{ old := storage }`. -/
  | stor (s : LStor)
  /-- A memory local bound to the `k`-th object the updates allocated. -/
  | mref (k : Nat)
  deriving Inhabited

/-- The updates so far: the names bound, newest first, the storage, and the
objects allocated. -/
structure Sym where
  env : List (Var × SymB)
  stor : LStor
  mem : SMem LTerm := []

/-- No update yet. -/
def Sym.empty : Sym := ⟨[], .init, []⟩

variable {C : Contract}

/-- A path whose key is not an integer: what an alias bound to a value
resolves to. -/
def LPath.stuck : LPath := .at (.root "") .err

/-- What a storage write stores: a word, or the subtree at a path of a
storage (`alice = bob;`). -/
inductive LVal where
  | word (t : LTerm)
  | sub (s : LStor) (q : LPath)
  /-- `new R(n)`'s value, copied into memory. -/
  | arr (R : RefTy) (n : LTerm)
  /-- The object `i` of the memory `m`, copied back (`copyMem`). -/
  | mem (m : LMem) (i : LId)
  deriving Inhabited

/-- What a storage write takes: a word or a subtree, not a fresh array. -/
def LVal.storable : LVal → Bool
  | .word _ | .sub _ _ => true
  | .arr _ _ | .mem _ _ => false

/-- What `toL` gives at each sort: a value an `LTerm`, a path an `LPath`, a
storage an `LStor`, a stored value an `LVal`; a memory sort its symbolic
reading with the term that returns exactly where it does (none outside the
fragment): an identity the offset of an object, an address the object and
what selects in it, a memory the objects, a memory value the slot. -/
@[reducible] def _root_.Solidity.Srt.LTy : Srt → Type
  | .val => LTerm
  | .path => LPath
  | .st => LStor
  | .sv => LVal
  | .ident => Option (Nat × LTerm)
  | .addr => Option (Nat × MSel × LTerm)
  | .mem => Option (SMem LTerm × LTerm)
  | .mv => Option (SMV LTerm × LTerm)

/-- A constant with the updates `ρ` pushed in. -/
def _root_.Solidity.Op0.toL (ρ : Sym) : Op0 s → s.LTy
  | .lit v => .lit v
  | .env k => .env k
  | .root r => .root r
  | .storage => ρ.stor
  | .memory => some (ρ.mem, .lit (.bool true))

/-- A unary symbol over its argument's `toL`. -/
def _root_.Solidity.Op1.toL : Op1 a s → a.LTy → s.LTy
  | .unop op p, x => .unop op p x
  | .net, _ => .err
  | .netOf _, _ => .err
  | .delValue, _ => .err
  | .field f, x => .field x f
  | .next, _ => .stuck
  | .select _, _ => .init
  | .sval, x => .word x
  | .newArr R, x => .arr R x
  | .alloc R, m => m.bind fun p => (sallocR LTerm.lit p.1 R).map fun q => (q.2, p.2)
  | .mfield f, i => i.map fun p => (p.1, .fld f, p.2)
  | .addM R, m => m.bind fun p => (sallocR LTerm.lit p.1 R).map fun q => (q.1, p.2)
  | .mval, x => some (.val x, x)
  | .ref, i => i.map fun p => (.ref p.1, p.2)
  | .wt _, _ => .err

/-- A binary symbol over its arguments' `toL`. -/
def _root_.Solidity.Op2.toL : Op2 a b s → a.LTy → b.LTy → s.LTy
  | .binop op p, x, y => .binop op p x y
  | .find, x, y => .find x y
  | .len, x, y => .len x y
  | .read, m, a =>
    match m, a with
    | some (M, g), some (k, sel, g') =>
      match readL M k sel with
      | some r => seqL g (seqL g' r)
      | none => .err
    | _, _ => .err
  | .mlen, m, i =>
    match m, i with
    | some (M, g), some (k, g') =>
      match mlenL M k with
      | some r => seqL g (seqL g' r)
      | none => .err
    | _, _ => .err
  | .at, x, y => .at x y
  | .nextIn, _, _ => .stuck
  | .delAt, x, y => .del x y
  | .pushSlot E, x, y => .arr (.slot E) x y (.lit (.bool true))
  | .pop, x, y => .arr (.pop false) x y (.lit (.bool true))
  | .shrink, x, y => .arr (.pop true) x y (.lit (.bool true))
  | .extend E, x, y => .arr (.slot E) x y (.lit (.bool true))
  | .sfind, x, y => .sub x y
  | .copyMem, _, _ => .word .err
  | .iread, m, a =>
    match m, a with
    | some (M, g), some (k, sel, g') => (ireadL M k sel).map fun k' => (k', seqL g g')
    | _, _ => none
  | .copy, m, v =>
    match m, v with
    | some (M, g), .arr R n =>
      match n.ground? with
      | some (.int c) => (sallocNew LTerm.lit M R c).map fun q => (q.2, g)
      | _ => none
    | _, _ => none
  | .mat, i, t => i.map fun p => (p.1, .idx t, seqL p.2 (isIntL t))
  | .copySt, m, v =>
    match m, v with
    | some (M, g), .arr R n =>
      match n.ground? with
      | some (.int c) => (sallocNew LTerm.lit M R c).map fun q => (q.1, g)
      | _ => none
    | _, _ => none

/-- A ternary symbol over its arguments' `toL`. -/
def _root_.Solidity.Op3.toL : Op3 a b c s → a.LTy → b.LTy → c.LTy → s.LTy
  | .ite, x, y, z => .ite x y z
  | .save, x, y, .word t => .save x y t
  | .save, x, y, .sub s q => .copy x y s q
  | .save, x, _, .arr _ _ | .save, x, _, .mem _ _ => x
  | .push, x, y, .word t => .arr .push x y t
  | .push, x, y, .sub s q =>
    .copy (.arr (.slot .uint) x y (.lit (.bool true))) (.at y (.len x y)) s q
  | .push, x, _, .arr _ _ | .push, x, _, .mem _ _ => x
  | .atIn, _, _, _ => .stuck
  | .write, m, a, v =>
    match m, a, v with
    | some (M, g), some (k, sel, g'), some (s, g'') =>
      (writeL M k sel s).map fun q => (q.1, seqL g'' (seqL g (seqL g' q.2)))
    | _, _, _ => none

/-- The path has no index: `alice.account`, not `people[i]`. -/
def LPath.noAt : LPath → Bool
  | .root _ => true
  | .field q _ => q.noAt
  | .at _ _ => false

/-- The path up to its last index: `people[i]` of `people[i].age`; none for
`alice.account`. -/
def LPath.lastAt : LPath → Option LPath
  | .root _ => none
  | .field q _ => q.lastAt
  | .at q k => some (.at q k)

/-- What makes binding an alias to `q` return, in the storage `s`: its keys
return, and every index on it is in bounds where the program checks it
(`State.checkIndex`), which is the location up to the last index being there
(`LStor.hasU`). -/
def guardPath (s : LStor) (q : LPath) : LTerm :=
  match q.lastAt with
  | none => .pok q
  | some q' => .seq (.pok q) (.has s q')

/-- The storage a storage variable is bound to: `old` of `{ old := storage }`. -/
def _root_.Solidity.Tm.storLocal? (ρ : Sym) : Tm C .st → Option LStor
  | .pvS x =>
    match lookupBy x ρ.env with
    | some (.stor s) => some s
    | _ => none
  | _ => none

/-- A binary symbol over its arguments' `toL`, a read of a storage variable
apart: `find(old, p)` is the path checked against the storage the updates
left (`guardPath`), then the snapshot read there (`LTerm.findP`), as the
program's read is. -/
def _root_.Solidity.Op2.toLAt (ρ : Sym) : Op2 a b s → Tm C a → a.LTy → b.LTy → s.LTy
  | .find, t, x, y =>
    match t.storLocal? ρ with
    | some st => .seq (guardPath ρ.stor y) (.findP st y)
    | none => .find x y
  | o, _, x, y => o.toL x y

theorem _root_.Solidity.Tm.storLocal?_isSome {ρ : Sym} {s : Tm C .st}
    (h : (s.storLocal? ρ).isSome = true) :
    ∃ x S, s = .pvS x ∧ lookupBy x ρ.env = some (.stor S) := by
  unfold Tm.storLocal? at h
  split at h
  · rename_i x
    split at h
    · rename_i S hl
      exact ⟨x, S, rfl, hl⟩
    · simp only [Option.isSome_none, Bool.false_eq_true] at h
  · simp only [Option.isSome_none, Bool.false_eq_true] at h

/-- A term with the updates `ρ` pushed in: after `{ y := find(storage,
balances[k]) }`, `y` is that read; after `{ sp1 := alice.account }`,
`sp1.balance` is `alice.account.balance`; after `{ storage := save(storage,
balances[k], 5) }`, `storage` is that write. -/
def _root_.Solidity.Tm.toL (ρ : Sym) : Tm C s → s.LTy
  | .pvV x =>
    match lookupBy x ρ.env with
    | some (.val t) => t
    | some (.path _) | some .stale | some (.stor _) | some (.mref _) => .err
    | none => .var x
  | .pvP x =>
    match lookupBy x ρ.env with
    | some (.path q) => q
    | _ => .stuck
  | .pvS _ => .init
  | .pvI x =>
    match lookupBy x ρ.env with
    | some (.mref k) => some (k, .lit (.bool true))
    | _ => none
  | .app0 o => o.toL ρ
  | .app1 o a => o.toL (a.toL ρ)
  | .app2 o a b => Op2.toLAt ρ o a (a.toL ρ) (b.toL ρ)
  | .app3 o a b c => o.toL (a.toL ρ) (b.toL ρ) (c.toL ρ)

/-- A write to the storage leaves an alias through an index stale: the
program checked it against the storage before. -/
def SymB.onWrite : SymB → SymB
  | .path q => if q.noAt then .path q else .stale
  | b => b

/-- The locals a symbol reads. -/
def SymB.vars : SymB → List Var
  | .val t => t.vars
  | .path q => q.vars
  | .stale => []
  | .stor s => s.vars
  | .mref _ => []

/-- The locals the updates so far read: a quantifier may bind none of them. -/
def Sym.vars (ρ : Sym) : List Var :=
  ρ.stor.vars ++ ρ.env.flatMap (fun b => b.2.vars) ++
    ρ.mem.flatMap fun o => o.leaves.flatMap LTerm.vars

/-- The updates so far, with `x` free again: bound by a quantifier, `x` is
the local itself. -/
def Sym.free (ρ : Sym) (x : Var) : Sym := { ρ with env := (x, .val (.var x)) :: ρ.env }

/-- The storage the updates left, `storage`. -/
def _root_.Solidity.Tm.isStorage : Tm C s → Bool
  | .app0 .storage => true
  | _ => false

theorem _root_.Solidity.STerm.isStorage_eq {s : STerm C} (h : s.isStorage = true) :
    s = .storage := by
  unfold Tm.isStorage at h
  split at h
  · rfl
  · cases h

/-- A constant in the fragment: a literal, a value of the transaction, a
root, `storage`. -/
def _root_.Solidity.Op0.inL : Op0 s → Bool
  | .lit _ | .env _ | .root _ | .storage | .memory => true

/-- A unary symbol in the fragment, its argument in it (`hb`); an
allocation where the default has no mapping. -/
def _root_.Solidity.Op1.inL : Op1 a s → a.LTy → Bool → Bool
  | .unop .., _, hb | .field _, _, hb | .sval, _, hb => hb
  | .newArr _, _, hb | .mfield _, _, hb | .mval, _, hb | .ref, _, hb => hb
  | .alloc R, x, hb => hb && Option.isSome (Op1.toL (.alloc R) x)
  | .addM R, x, hb => hb && Option.isSome (Op1.toL (.addM R) x)
  | _, _, _ => false

/-- The read is of an object the updates allocated. -/
def readOk : Option (SMem LTerm × LTerm) → Option (Nat × MSel × LTerm) → Bool
  | some (M, _), some (k, sel, _) => (readL M k sel).isSome
  | _, _ => false

/-- The length is of an object the updates allocated. -/
def mlenOk : Option (SMem LTerm × LTerm) → Option (Nat × LTerm) → Bool
  | some (M, _), some (k, _) => (mlenL M k).isSome
  | _, _ => false

/-- A binary symbol in the fragment, its arguments in it (`ha`, `hb`); a
read or a delete is of `storage` itself. -/
def _root_.Solidity.Op2.inL (ρ : Sym) : Op2 a b s → Tm C a → a.LTy → b.LTy → Bool → Bool → Bool
  | .binop .., _, _, _, ha, hb | .at, _, _, _, ha, hb => ha && hb
  | .find, s, _, _, _, hb => (s.isStorage || (s.storLocal? ρ).isSome) && hb
  | .len, s, _, _, _, hb | .delAt, s, _, _, _, hb | .sfind, s, _, _, _, hb => s.isStorage && hb
  | .pushSlot _, s, _, _, _, hb | .extend _, s, _, _, _, hb | .pop, s, _, _, _, hb
  | .shrink, s, _, _, _, hb =>
    s.isStorage && hb
  | .read, _, x, y, ha, hb => ha && hb && readOk x y
  | .mlen, _, x, y, ha, hb => ha && hb && mlenOk x y
  | .mat, _, _, _, ha, hb => ha && hb
  | .iread, _, x, y, ha, hb => ha && hb && Option.isSome (Op2.toL .iread x y)
  | .copy, _, x, y, ha, hb => ha && hb && Option.isSome (Op2.toL .copy x y)
  | .copySt, _, x, y, ha, hb => ha && hb && Option.isSome (Op2.toL .copySt x y)
  | _, _, _, _, _, _ => false

/-- A ternary symbol in the fragment: a conditional, or a write or a push
over `storage` itself; a push of a word. -/
def _root_.Solidity.Op3.inL : Op3 a b c s → Tm C a → Tm C c → a.LTy → b.LTy → c.LTy →
    Bool → Bool → Bool → Bool
  | .ite, _, _, _, _, _, hc, ha, hb => hc && ha && hb
  | .save, s, _, _, _, z, _, hp, hv => s.isStorage && hp && hv && z.storable
  | .push, s, .app1 .sval _, _, _, _, _, hp, hv | .push, s, .app2 .sfind _ _, _, _, _, _, hp, hv =>
    s.isStorage && hp && hv
  | .write, _, _, x, y, z, hm, ha, hv => hm && ha && hv && Option.isSome (Op3.toL .write x y z)
  | _, _, _, _, _, _, _, _, _ => false

/-- The fragment: storage values and paths only, every alias bound by an
update.  A read is of the storage the updates left, `find(storage, p)`: its
path is checked against that storage, and read there.  A path's alias only
where an update bound it (`Person storage p = alice;` does), and to a path
with no index.  A storage: one write, one `delete`, one `push` of a word or
`push()`, or one `pop`, over the storage the updates left.  A storage
variable (`old`) bound by an update, read at a path the storage the updates
left checks.  A stored value: a word, or a copy of a subtree of the storage
the updates left (`alice = bob;`). -/
def _root_.Solidity.Tm.inL (ρ : Sym) : Tm C s → Bool
  | .pvV _ => true
  | .pvP x =>
    match lookupBy x ρ.env with
    | some (.path _) | some (.val _) => true
    | some .stale | some (.stor _) | some (.mref _) | none => false
  | .pvS _ => false
  | .pvI x =>
    match lookupBy x ρ.env with
    | some (.mref _) => true
    | _ => false
  | .app0 o => o.inL
  | .app1 o a => o.inL (a.toL ρ) (a.inL ρ)
  | .app2 o a b => o.inL ρ a (a.toL ρ) (b.toL ρ) (a.inL ρ) (b.inL ρ)
  | .app3 o a b c => o.inL a c (a.toL ρ) (b.toL ρ) (c.toL ρ) (a.inL ρ) (b.inL ρ) (c.inL ρ)


/-- A unary symbol of `sameShape`: `¬`, a member. -/
def _root_.Solidity.Op1.shape : Op1 a s → Bool → Bool
  | .unop .., b | .field _, b => b
  | _, _ => false

/-- A storage variable: `old`. -/
def _root_.Solidity.Tm.isPvS : Tm C .st → Bool
  | .pvS _ => true
  | _ => false

/-- A binary symbol of `sameShape`: an operator, an index, a read of `storage`
or of a storage variable. -/
def _root_.Solidity.Op2.shape : Op2 a b s → Tm C a → Bool → Bool → Bool
  | .binop .., _, x, y | .at, _, x, y => x && y
  | .find, s, _, y => (s.isStorage || s.isPvS) && y
  | .len, s, _, y => s.isStorage && y
  | _, _, _, _ => false

/-- The terms `sameL` compares: literals, values of the transaction, locals,
operators, conditionals and reads of `storage`, over paths of roots, aliases,
members and indices. -/
def _root_.Solidity.Tm.sameShape : Tm C s → Bool
  | .pvV _ | .pvP _ => true
  | .pvS _ | .pvI _ => false
  | .app0 o => match o with
    | .lit _ | .env _ | .root _ => true
    | _ => false
  | .app1 o a => o.shape a.sameShape
  | .app2 o a b => o.shape a a.sameShape b.sameShape
  | .app3 o a b c => match o with
    | .ite => a.sameShape && b.sameShape && c.sameShape
    | _ => false

/-- The same term of the fragment, as a `Bool` the kernel computes: how
`Fml.inL` recognises `eqD a b` (`Fml.eqDView`).  Outside the fragment it is
`false`, which only narrows the fragment. -/
def _root_.Solidity.Tm.sameL (a b : Tm C s) : Bool := a.sameShape && decide (a = b)

/-- `eqD a b`, `defined a ∧ (defined b ∧ a = b)` (`Update.lean`), split at
its outer conjunction: the equation of the fragment.  A bare `a = b` reads
the Theory (`holds`), where a term that halts still denotes something, so
the fragment takes an equation only with both sides defined. -/
def _root_.Solidity.Fml.eqDView : Fml C → Fml C → Option (Term C × Term C)
  | .defined a, .and (.defined b) (.eq a' b') =>
    if a.sameL a' && b.sameL b' then some (a, b) else none
  | _, _ => none

/-- A literal or a local: a term whose Theory value is its value where it
returns, and no primitive where it halts (`Term.atom_equiv_prim`). -/
def _root_.Solidity.Term.isAtom : Term C → Bool
  | .lit _ | .pv _ => true
  | _ => false

/-- A literal, or a value of the transaction (`msg.sender`): a term that
returns one value, the same in every state the updates reach. -/
def _root_.Solidity.Term.isLitLike : Term C → Bool
  | .lit _ | .env _ => true
  | _ => false

/-- A total equation `a ≐ b` the fragment takes: a literal (or `msg.sender`)
against a literal or a local, `se1 ≐ true` of a symbolically executed `if`,
`msg.sender ≐ r` of a precondition.  There the total reading is the partial
one (`Fml.toL_holds`); `x ≐ y` of two unbound locals is not, since both
denote the empty struct. -/
def _root_.Solidity.Term.eqLit (a b : Term C) : Bool :=
  (a.isLitLike && b.isAtom) || (b.isLitLike && a.isAtom)

/-- What returns exactly where the amount `a` of a payment is not
negative: `a < 0 ? err : true`. -/
def payGuard (a : LTerm) : LTerm :=
  .ite (.binop .lt .uint a (.lit (.int 0))) .err (.lit (.bool true))

theorem payGuard_eval (σ : State) (a : LTerm) {y : Value} {j : Int} (ha : a.eval σ = .ok y)
    (hj : y.asInt = .ok j) : (payGuard a).eval σ =
      if j < 0 then .error .stuck else .ok (.bool true) := by
  cases y with
  | bool b => simp only [Value.asInt, reduceCtorEq] at hj
  | int n =>
    simp only [Value.asInt, Except.ok.injEq] at hj
    subst hj
    by_cases hn : n < 0 <;>
      simp only [payGuard, LTerm.eval, bind, Except.bind, ha, evalBinop, applyBinOp, Value.asInt,
          hn, decide_true, checkArith, pickBranch, ↓reduceIte, decide_false]

/-- One update: the term that has to return, and the names it binds. -/
def _root_.Solidity.UpdElem.toL (ρ : Sym) : UpdElem C → LTerm × Sym
  | .val x t => (t.toL ρ, { ρ with env := (x, .val (t.toL ρ)) :: ρ.env })
  | .path x p =>
    (guardPath ρ.stor (p.toL ρ), { ρ with env := (x, .path (p.toL ρ)) :: ρ.env })
  | .storage s =>
    (.sok (s.toL ρ), { ρ with stor := s.toL ρ, env := ρ.env.map fun b => (b.1, b.2.onWrite) })
  | .store x s => (.sok (s.toL ρ), { ρ with env := (x, .stor (s.toL ρ)) :: ρ.env })
  -- a ledger entry: it returns where the address and the amount are integers,
  -- which `kite` asks; the ledger itself is not pushed in (nothing reads it)
  | .net r _ a => (.kite (r.toL ρ) (a.toL ρ) (.lit (.bool true)) (.lit (.bool true)), ρ)
  -- a payment: the same, and the amount not negative
  | .pay r a => (.kite (r.toL ρ) (a.toL ρ) (payGuard (a.toL ρ)) (payGuard (a.toL ρ)), ρ)
  | .mref x i =>
    match i.toL ρ with
    | some (k, g) => (g, { ρ with env := (x, .mref k) :: ρ.env })
    | none => (.err, ρ)
  | .memory m =>
    match m.toL ρ with
    | some (M, g) => (g, { ρ with mem := M })
    | none => (.err, ρ)
  | .selfBalance .. | .saveNet .. => (.err, ρ)

/-- An update in the fragment: a local, an alias, the storage, a storage
variable bound to it, or a ledger entry (`transfer`'s, which no term of the
fragment reads); no memory, no funds. -/
def _root_.Solidity.UpdElem.inL (ρ : Sym) : UpdElem C → Bool
  | .val _ t => t.inL ρ
  | .path _ p => p.inL ρ
  | .storage s | .store _ s => s.inL ρ
  | .net r _ a | .pay r a => r.inL ρ && a.inL ρ
  | .mref _ i => i.inL ρ
  | .memory m => m.inL ρ
  | .selfBalance .. | .saveNet .. => false

/-- The update's term as a premise (box) or a conjunct (diamond). -/
def guardM : Modality → LTerm → LFml → LFml
  | .box, g, φ => .imp (.eq g g) φ
  | .diamond, g, φ => .and (.eq g g) φ

/-- A program that starts with `revert();`: it halts, whatever follows. -/
def _root_.Solidity.Prog.reverts : Prog C → Bool
  | .revert :: _ => true
  | _ => false

theorem _root_.Solidity.Prog.reverts_eq {P : Prog C} (h : P.reverts = true) :
    ∃ ω, P = .revert :: ω := by
  unfold Prog.reverts at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-- A formula with its updates pushed in. -/
def _root_.Solidity.Fml.toL : Sym → Fml C → LFml
  | _, .tt => .tt
  | ρ, .eq a b => .eq (a.toL ρ) (b.toL ρ)
  | ρ, .defined t => .eq (t.toL ρ) (t.toL ρ)
  | ρ, .not φ => .not (φ.toL ρ)
  | ρ, .and φ ψ =>
    match Fml.eqDView φ ψ with
    | some (a, b) => .eq (a.toL ρ) (b.toL ρ)
    | none => .and (φ.toL ρ) (ψ.toL ρ)
  | ρ, .imp φ ψ => .imp (φ.toL ρ) (ψ.toL ρ)
  | ρ, .upd _ [] φ => φ.toL ρ
  | ρ, .upd m [e] φ => guardM m (e.toL ρ).1 (φ.toL (e.toL ρ).2)
  | _, .modal .box _ _ => .tt
  | _, .modal .diamond _ _ => .not .tt
  | ρ, .all x p φ => .all x p (φ.toL (ρ.free x))
  | _, .upd _ (_ :: _ :: _) _ | _, .havoc _ => .tt

/-- The fragment `Fml.toL` is exact on: no modality, one element per update,
no memory, and every alias bound by an update. -/
def _root_.Solidity.Fml.inL : Sym → Fml C → Bool
  | _, .tt => true
  | _, .eq a b => a.eqLit b
  | ρ, .defined t => t.inL ρ
  | ρ, .not φ => φ.inL ρ
  | ρ, .and φ ψ =>
    match Fml.eqDView φ ψ with
    | some (a, b) => a.inL ρ && b.inL ρ
    | none => φ.inL ρ && ψ.inL ρ
  | ρ, .imp φ ψ => φ.inL ρ && ψ.inL ρ
  | ρ, .upd _ [] φ => φ.inL ρ
  | ρ, .upd _ [e] φ => e.inL ρ && φ.inL (e.toL ρ).2
  | _, .modal _ P _ => P.reverts
  | ρ, .all x _ φ => !ρ.vars.contains x && φ.inL (ρ.free x)
  | _, .upd _ (_ :: _ :: _) _ | _, .havoc _ => false


/-! ### The updates pushed in keep the meaning -/

/-- The storage as one tree reads at `r.segs` what the storage reads at the
root `r`: `balances[k]` is `[balances, k]`. -/
theorem find_root (τ : State) (r : Name) (segs : List Seg) :
    (SVal.struct τ.storage).find (.field r :: segs) = τ.findStorage r segs := by
  simp only [SVal.find, State.findStorage]

/-- A write at the root `r` of the one tree is `saveStorage` at `r`:
`balances[k] = 5;` either way. -/
theorem save_root (τ : State) (r : Name) (segs : List Seg) (new : SVal) :
    (SVal.struct τ.storage).save (.field r :: segs) new =
      τ.saveStorage r segs new >>= fun τ' => .ok (.struct τ'.storage) := by
  simp only [SVal.save, State.saveStorage]
  cases hl : lookupBy r τ.storage with
  | none => rfl
  | some v =>
    simp only
    cases hs : v.save segs new <;> simp only [bind, Except.bind]

/-- A path up to its last index: `[people, at i]` of `[people, at i, age]`. -/
def lastAtSegs (qs : List Seg) : List Seg := (qs.reverse.dropWhile fun s => !Seg.isAt s).reverse

/-- Every index of the path is in bounds of what the storage holds live:
the location up to the last index is there, live.  What the program's checks
leave of a path it took (`PTerm.toL_chk`). -/
def LiveTo (T : SVal) (qs : List Seg) : Prop := ∃ c, T.findLive (lastAtSegs qs) = .ok c

/-- What a name holds after the updates, against what its symbol says. -/
def EnvRel (σ τ : State) (x : Var) : Option SymB → Prop
  | none => τ.getEnv x = σ.getEnv x
  | some (.val t) => ∃ v, t.eval σ = .ok v ∧ τ.getEnv x = .ok (.val v)
  | some (.path q) => ∃ r segs, q.eval σ = .ok (.field r :: segs) ∧
      τ.getEnv x = .ok (.spath r segs) ∧ LiveTo (.struct τ.storage) (.field r :: segs)
  | some .stale => ∃ r segs, τ.getEnv x = .ok (.spath r segs)
  | some (.stor s) => ∃ st, s.eval σ = .ok (.struct st) ∧ τ.getEnv x = .ok (.store st)
  | some (.mref k) => τ.getEnv x = .ok (.mref (σ.nextId + k))

/-- `τ` is what the updates `ρ` stand for, applied in `σ`: its storage is the
stack of writes read in `σ`, each name holds what its symbol reads in `σ`,
and its heap the objects allocated, from `σ`'s `nextId` on. -/
structure Rel (σ : State) (ρ : Sym) (τ : State) : Prop where
  stor : ρ.stor.eval σ = .ok (.struct τ.storage)
  env : ∀ x, EnvRel σ τ x (lookupBy x ρ.env)
  tx : ∀ k, τ.envVal k = σ.envVal k
  mem : MemRel (fun t => t.eval σ) σ.nextId ρ.mem τ

/-- Before any update, the state is itself. -/
theorem Rel.empty (σ : State) : Rel σ Sym.empty σ :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, MemRel.empty _ σ⟩

/-- Binding a name keeps the relation: after `uint y = balances[k];`, `y`
holds what `balances[k]` reads. -/
theorem Rel.bind {σ τ : State} {ρ : Sym} (h : Rel σ ρ τ) (x : Var) (b : SymB) (bd : Binding)
    (hb : EnvRel σ (τ.setEnv x bd) x (some b)) :
    Rel σ { ρ with env := (x, b) :: ρ.env } (τ.setEnv x bd) := by
  refine ⟨h.stor, fun y => ?_, fun k => by rw [← h.tx k]; cases k <;> rfl,
    h.mem.of_heap rfl rfl⟩
  by_cases hy : y = x
  · subst hy; simpa only [lookupBy, ↓reduceIte] using hb
  · have := h.env y
    simp only [lookupBy, hy, if_false]
    revert this
    have hst : (τ.setEnv x bd).storage = τ.storage := rfl
    rcases lookupBy y ρ.env with _ | ⟨t⟩ | ⟨q⟩ | _ <;>
      simp only [EnvRel, State.getEnv_setEnv_ne hy, imp_self, hst]

/-- The word terms of the heap read only what the updates read. -/
theorem mem_vars {x : Var} {M : SMem LTerm} (hx : x ∉ M.flatMap fun o => o.leaves.flatMap LTerm.vars) :
    ∀ o ∈ M, ∀ t ∈ o.leaves, x ∉ t.vars := by
  intro o ho t ht hxt
  exact hx (List.mem_flatMap.2 ⟨o, ho, List.mem_flatMap.2 ⟨t, ht, hxt⟩⟩)

/-- A symbol the updates bound reads only what the updates read. -/
theorem lookupBy_vars {x y : Var} {b : SymB} : (env : List (Var × SymB)) →
    lookupBy y env = some b → x ∉ env.flatMap (fun b => b.2.vars) → x ∉ b.vars
  | [], h, _ => by simp only [lookupBy, reduceCtorEq] at h
  | (z, c) :: rest, h, hx => by
    simp only [List.flatMap_cons, List.mem_append, not_or] at hx
    by_cases hz : y = z
    · simp only [lookupBy, hz, if_true, Option.some.injEq] at h
      subst h; exact hx.1
    · simp only [lookupBy, hz, if_false] at h
      exact lookupBy_vars rest h hx.2

/-- Rebinding a local the updates do not read keeps the relation, the local
now free: what a quantifier does. -/
theorem Rel.free {σ τ : State} {ρ : Sym} (h : Rel σ ρ τ) {x : Var} (hx : x ∉ ρ.vars)
    (v : Value) : Rel (σ.setEnv x (.val v)) (ρ.free x) (τ.setEnv x (.val v)) := by
  simp only [Sym.vars, List.mem_append, not_or] at hx
  obtain ⟨⟨hx₁, hx₂⟩, hx₃⟩ := hx
  refine ⟨?_, fun y => ?_, fun k => by
    rw [State.envVal_setEnv, State.envVal_setEnv, h.tx k],
    (h.mem.congr fun o ho t ht => LTerm.eval_setEnv t (mem_vars hx₃ o ho t ht)).of_heap
      rfl rfl⟩
  · show LStor.eval (σ.setEnv x (.val v)) ρ.stor = _
    rw [LStor.eval_setEnv _ hx₁]; exact h.stor
  · by_cases hy : y = x
    · subst hy
      simp only [Sym.free, lookupBy, if_true, EnvRel, LTerm.eval]
      exact ⟨v, by simp only [State.getEnv_setEnv_self]; rfl,
          by simp only [State.getEnv_setEnv_self]⟩
    · have hl : lookupBy y (ρ.free x).env = lookupBy y ρ.env := by
        simp only [Sym.free, lookupBy, hy, ↓reduceIte]
      rw [hl]
      have he := h.env y
      rcases hb : lookupBy y ρ.env with _ | ⟨t⟩ | ⟨q⟩ | _ | ⟨S⟩ | ⟨k⟩ <;> rw [hb] at he <;>
        simp only [EnvRel] at he ⊢ <;>
        simp only [State.getEnv_setEnv_ne hy]
      · exact he
      · have hv := lookupBy_vars (x := x) ρ.env hb hx₂
        simp only [SymB.vars] at hv
        rw [LTerm.eval_setEnv _ hv]; exact he
      · have hv := lookupBy_vars (x := x) ρ.env hb hx₂
        simp only [SymB.vars] at hv
        rw [LPath.eval_setEnv _ hv]; exact he
      · exact he
      · have hv := lookupBy_vars (x := x) ρ.env hb hx₂
        simp only [SymB.vars] at hv
        rw [LStor.eval_setEnv _ hv]; exact he
      · exact he

/-! ### Checked paths, slot reads and live reads

The program checks each index of a path against the live length where it
takes the path (`State.checkIndex`), and then reads or writes the slot; the
target language reads and writes the live storage with no check.  Where the
path was checked against the storage it reads, the two agree
(`PTerm.toL_chk`, `live_bridge`). -/

/-- A path with no index evaluates to one. -/
theorem LPath.noAt_eval (σ : State) : ∀ {q : LPath} {qs : List Seg}, q.noAt = true →
    q.eval σ = .ok qs → qs.any Seg.isAt = false
  | .root _, _, _, h => by cases h; rfl
  | .field q f, _, hn, h => by
    obtain ⟨qs', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    simp only [LPath.noAt] at hn
    simp only [List.any_append, LPath.noAt_eval σ hn h', List.any_cons, Seg.isAt, List.any_nil,
        Bool.or_self]
  | .at _ _, _, hn, _ => by simp only [noAt, Bool.false_eq_true] at hn

/-- With no index on the way, the live read is the read: `alice.account`. -/
theorem findLive_eq_find : ∀ (v : SVal) (qs : List Seg), qs.any Seg.isAt = false →
    v.findLive qs = v.find qs
  | v, [], _ => by cases v <;> rfl
  | _, .at _ :: _, h => by simp only [List.any_cons, Seg.isAt, Bool.true_or,
      Bool.true_eq_false] at h
  | v, .field f :: qs, h => by
    have h' : qs.any Seg.isAt = false := by simpa only [List.any_eq_false, Seg.isAt,
        Bool.not_eq_true, List.any_cons, Bool.false_or] using h
    cases v with
    | prim _ => rfl
    | struct fields =>
      simp only [SVal.findLive, SVal.find]
      cases lookupBy f fields with
      | none => rfl
      | some w => exact findLive_eq_find w qs h'
    | array elems shadow fx =>
      by_cases hf : f = "length"
      · subst hf
        simp only [SVal.findLive, SVal.find]
        cases fx
        · exact findLive_eq_find _ qs h'
        · rfl
      · simp only [SVal.findLive, SVal.find]
    | map _ _ => rfl

/-- **One index**: the program's check (`Close.idxOk`) passes exactly where
the live element is there: `values[1]` with two values, `balances[k]`. -/
theorem idx_iff (c : SVal) (k : Int) :
    Close.idxOk k c = .ok () ↔ ∃ c', c.findLive [.at k] = .ok c' := by
  cases c with
  | prim p => simp only [Close.idxOk, reduceCtorEq, SVal.findLive, exists_false]
  | struct _ => simp only [Close.idxOk, reduceCtorEq, SVal.findLive, exists_false]
  | array elems shadow fx =>
    by_cases hk : 0 ≤ k ∧ k.toNat < elems.length
    · simp only [Close.idxOk, hk, and_self, ↓reduceIte, SVal.findLive, ↓reduceDIte,
        List.get_eq_getElem, SVal.findLive_nil, Except.ok.injEq, exists_eq']
    · simp only [Close.idxOk, hk, ↓reduceIte, reduceCtorEq, SVal.findLive, ↓reduceDIte,
        exists_false]
  | map entries dflt =>
    simp only [Close.idxOk, SVal.findLive, true_iff]
    cases lookupBy k entries <;> simp only [Except.ok.injEq, exists_eq']

/-- A live write whose path reads live is the write. -/
theorem saveLive_eq_save : ∀ {v : SVal} {qs : List Seg} {c : SVal} (new : SVal),
    v.findLive qs = .ok c → v.saveLive qs new = v.save qs new
  | v, [], _, _, _ => by cases v <;> rfl
  | .prim _, _ :: _, _, _, h => by simp only [SVal.findLive, reduceCtorEq] at h
  | .struct fields, .field f :: qs, _, new, h => by
    simp only [SVal.findLive] at h
    simp only [SVal.saveLive, SVal.save]
    split at h
    · rename_i o hl
      rw [hl]
      simp only [saveLive_eq_save new h]
    · simp only [reduceCtorEq] at h
  | .struct _, .at _ :: _, _, _, h => by simp only [SVal.findLive, reduceCtorEq] at h
  | .array elems shadow fx, .at i :: qs, _, new, h => by
    simp only [SVal.findLive] at h
    split at h
    · rename_i hi
      have hi' : 0 ≤ i ∧ i.toNat < (elems ++ shadow).length := ⟨hi.1,
          by simp only [List.length_append]; omega⟩
      simp only [SVal.saveLive, SVal.save, dif_pos hi, dif_pos hi', List.get_eq_getElem,
        List.getElem_append_left hi.2]
      rw [List.get_eq_getElem] at h
      rw [saveLive_eq_save new h]
      cases (elems[i.toNat]'hi.2).save qs new with
      | error _ => rfl
      | ok u =>
        simp only [bind, Except.bind]
        rw [List.set_append_left _ _ hi.2]
        simp only [List.length_set, List.take_left', List.drop_left']
    · simp only [reduceCtorEq] at h
  | .array _ _ _, .field _ :: _, _, _, _ => by simp only [SVal.saveLive, SVal.save]
  | .map entries dflt, .at i :: qs, _, new, h => by
    simp only [SVal.findLive] at h
    simp only [SVal.saveLive, SVal.save]
    split at h <;> rename_i hl <;> rw [hl] <;> simp only [saveLive_eq_save new h]
  | .map _ _, .field _ :: _, _, _, _ => by simp only [SVal.saveLive, SVal.save]

/-- A live write returns only where the live read does. -/
theorem findLive_of_saveLive : ∀ {v : SVal} {qs : List Seg} {new u : SVal},
    v.saveLive qs new = .ok u → ∃ c, v.findLive qs = .ok c
  | v, [], _, _, _ => ⟨v, by cases v <;> rfl⟩
  | .prim _, s :: _, _, _, h => by cases s <;> simp only [SVal.saveLive, reduceCtorEq] at h
  | .struct fields, .field f :: qs, _, _, h => by
    simp only [SVal.saveLive] at h
    simp only [SVal.findLive]
    split at h
    · rename_i o hl
      obtain ⟨_, hu, _⟩ := Res.bind_eq_ok.1 h
      rw [hl]
      exact findLive_of_saveLive hu
    · simp only [reduceCtorEq] at h
  | .struct _, .at _ :: _, _, _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .array elems shadow fx, .at i :: qs, _, _, h => by
    simp only [SVal.saveLive] at h
    simp only [SVal.findLive]
    split at h
    · rename_i hi
      obtain ⟨_, hu, _⟩ := Res.bind_eq_ok.1 h
      rw [dif_pos hi]
      exact findLive_of_saveLive hu
    · simp only [reduceCtorEq] at h
  | .array _ _ _, .field _ :: _, _, _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .map entries dflt, .at i :: qs, _, _, h => by
    simp only [SVal.saveLive] at h
    simp only [SVal.findLive]
    split at h <;> rename_i hl <;> rw [hl] <;>
      (obtain ⟨_, hu, _⟩ := Res.bind_eq_ok.1 h; exact findLive_of_saveLive hu)
  | .map _ _, .field _ :: _, _, _, h => by simp only [SVal.saveLive, reduceCtorEq] at h

/-- A write returns only where the read does. -/
theorem find_of_save {v : SVal} {qs : List Seg} {new u : SVal} (h : v.save qs new = .ok u) :
    ∃ c, v.find qs = .ok c := by
  cases hf : v.find qs with
  | ok c => exact ⟨c, rfl⟩
  | error e => rw [Close.save_of_find_error hf] at h; cases h

/-! #### Up to the last index -/

/-- A member after the last index leaves it the last. -/
theorem lastAtSegs_field (qs : List Seg) (f : Name) :
    lastAtSegs (qs ++ [.field f]) = lastAtSegs qs := by
  simp only [lastAtSegs, Seg.isAt, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, Bool.not_false, List.dropWhile_cons_of_pos]

/-- An index is the last one. -/
theorem lastAtSegs_at (qs : List Seg) (k : Int) :
    lastAtSegs (qs ++ [.at k]) = qs ++ [.at k] := by
  simp only [lastAtSegs, Seg.isAt, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, Bool.not_true, Bool.false_eq_true, not_false_eq_true,
          List.dropWhile_cons_of_neg, List.reverse_reverse]

/-- A path is its part up to the last index, then members. -/
theorem lastAtSegs_split (qs : List Seg) :
    ∃ post, qs = lastAtSegs qs ++ post ∧ post.any Seg.isAt = false := by
  refine ⟨(qs.reverse.takeWhile fun s => !Seg.isAt s).reverse, ?_, ?_⟩
  · have := congrArg List.reverse
      (List.takeWhile_append_dropWhile (p := fun s => !Seg.isAt s) (l := qs.reverse))
    simp only [List.reverse_append, List.reverse_reverse] at this
    unfold lastAtSegs
    exact this.symm
  · have hall := List.all_takeWhile (p := fun s => !Seg.isAt s) (l := qs.reverse)
    simp only [List.all_eq_true] at hall
    simp only [List.any_eq_false, List.mem_reverse]
    intro s hs
    simpa only [Bool.not_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] using hall s hs

/-- A path with no index has nothing up to its last one. -/
theorem lastAtSegs_noAt {qs : List Seg} (h : qs.any Seg.isAt = false) : lastAtSegs qs = [] := by
  have hd : ∀ {l : List Seg}, (∀ s ∈ l, Seg.isAt s = false) →
      l.dropWhile (fun s => !Seg.isAt s) = [] := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.dropWhile_cons, hl a List.mem_cons_self, Bool.not_false, if_true]
      exact ih fun s hs => hl s (List.mem_cons_of_mem _ hs)
  simp only [lastAtSegs, List.reverse_eq_nil_iff]
  apply hd
  intro s hs
  simp only [List.any_eq_false] at h
  simpa only [Bool.not_eq_true] using h s (List.mem_reverse.mp hs)

/-- With every index in bounds, the slot read is the live read. -/
theorem LiveTo.find_eq {T : SVal} {qs : List Seg} (h : LiveTo T qs) : T.find qs = T.findLive qs := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨post, hq, hp⟩ := lastAtSegs_split qs
  rw [hq, SVal.find_append, SVal.findLive_append, hc, SVal.find_of_findLive hc, Res.ok_bind,
    Res.ok_bind, findLive_eq_find c post hp]

/-- A path read live has every index in bounds. -/
theorem LiveTo.of_findLive {T c : SVal} {qs : List Seg} (h : T.findLive qs = .ok c) :
    LiveTo T qs := by
  obtain ⟨post, hq, _⟩ := lastAtSegs_split qs
  rw [hq, SVal.findLive_append] at h
  obtain ⟨c₀, hc₀, -⟩ := Res.bind_eq_ok.1 h
  exact ⟨c₀, hc₀⟩

/-- A path with no index has none out of bounds. -/
theorem LiveTo.of_noAt (T : SVal) {qs : List Seg} (h : qs.any Seg.isAt = false) : LiveTo T qs :=
  ⟨T, by rw [lastAtSegs_noAt h]; cases T <;> rfl⟩

/-- The last index of a path, evaluated. -/
theorem LPath.lastAt_eval (σ : State) : ∀ {q : LPath} {qs : List Seg}, q.eval σ = .ok qs →
    (q.lastAt = none → qs.any Seg.isAt = false) ∧
      (∀ q', q.lastAt = some q' → q'.eval σ = .ok (lastAtSegs qs))
  | .root _, _, h => by cases h; exact ⟨fun _ => rfl, fun _ h => by simp only [lastAt,
      reduceCtorEq] at h⟩
  | .field q f, _, h => by
    obtain ⟨qs', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    obtain ⟨h₁, h₂⟩ := LPath.lastAt_eval σ h'
    refine ⟨fun hn => ?_, fun q' hs => ?_⟩
    · simp only [List.any_append, h₁ hn, List.any_cons, Seg.isAt, List.any_nil, Bool.or_self]
    · rw [lastAtSegs_field]; exact h₂ q' hs
  | .at q k, _, h => by
    refine ⟨fun hn => by simp only [lastAt, reduceCtorEq] at hn, fun q' hs => ?_⟩
    simp only [LPath.lastAt, Option.some.injEq] at hs
    subst hs
    obtain ⟨qs', h', h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨i, hi, he⟩ := Res.bind_eq_ok.1 h; cases he
    rw [lastAtSegs_at]
    simp only [LPath.eval, h', hi, Res.ok_bind]

/-- **Binding an alias returns** exactly where its path does and every
index on it is in bounds of the storage `s` leaves. -/
theorem guardPath_ok {σ : State} {s : LStor} {T : SVal} (hs : s.eval σ = .ok T) (q : LPath) :
    (∃ v, (guardPath s q).eval σ = .ok v) ↔ ∃ qs, q.eval σ = .ok qs ∧ LiveTo T qs := by
  unfold guardPath
  cases hl : q.lastAt with
  | none =>
    simp only [LTerm.eval, Res.bind_eq_ok]
    constructor
    · rintro ⟨_, qs, hq, -⟩
      exact ⟨qs, hq, LiveTo.of_noAt T ((LPath.lastAt_eval σ hq).1 hl)⟩
    · rintro ⟨qs, hq, -⟩
      exact ⟨_, qs, hq, rfl⟩
  | some q' =>
    simp only [LTerm.eval, Res.bind_eq_ok, hs, Res.ok_bind]
    constructor
    · rintro ⟨_, _, ⟨qs, hq, -⟩, qs', hq', c, hc, -⟩
      have := (LPath.lastAt_eval σ hq).2 q' hl
      rw [hq'] at this
      cases this
      exact ⟨qs, hq, c, hc⟩
    · rintro ⟨qs, hq, c, hc⟩
      exact ⟨_, _, ⟨qs, hq, rfl⟩, _, (LPath.lastAt_eval σ hq).2 q' hl, c, hc, rfl⟩

/-- **The read of a checked path is the live read**: given what the checks
of a path amount to (`PTerm.toL_chk`), a read returns the same either way. -/
theorem live_bridge {τ : State} {P : Res (Name × List Seg)} {L : Res (List Seg)}
    (hA : ∀ qs, (∃ rs, P = .ok rs ∧ qs = .field rs.1 :: rs.2) ↔
      (L = .ok qs ∧ LiveTo (.struct τ.storage) qs)) (qs : List Seg) (c : SVal) :
    (L = .ok qs ∧ (SVal.struct τ.storage).findLive qs = .ok c) ↔
      ∃ rs, P = .ok rs ∧ qs = .field rs.1 :: rs.2 ∧ τ.findStorage rs.1 rs.2 = .ok c := by
  constructor
  · rintro ⟨hq, hc⟩
    have hl := LiveTo.of_findLive hc
    obtain ⟨rs, hrs, rfl⟩ := (hA _).2 ⟨hq, hl⟩
    refine ⟨rs, hrs, rfl, ?_⟩
    rw [← find_root, hl.find_eq]
    exact hc
  · rintro ⟨rs, hrs, rfl, hc⟩
    obtain ⟨hq, hl⟩ := (hA _).1 ⟨rs, hrs, rfl⟩
    refine ⟨hq, ?_⟩
    rw [← hl.find_eq, find_root]
    exact hc

/-- **A read of the node at a checked path is the live read of it**, the
rest of the run alike: `live_bridge` under a bind. -/
theorem read_bridge {α : Type} {τ : State} {P : Res (Name × List Seg)} {L : Res (List Seg)}
    (hb : ∀ qs c, (L = .ok qs ∧ (SVal.struct τ.storage).findLive qs = .ok c) ↔
      ∃ rs, P = .ok rs ∧ qs = .field rs.1 :: rs.2 ∧ τ.findStorage rs.1 rs.2 = .ok c)
    {G G' : SVal → Res α} (hG : ∀ c, Sim (G c) (G' c)) :
    Sim (L >>= fun qs => (SVal.struct τ.storage).findLive qs >>= G)
      (P >>= fun rs => τ.findStorage rs.1 rs.2 >>= G') := by
  intro a
  simp only [Res.bind_eq_ok]
  constructor
  · rintro ⟨qs, hq, c, hc, ha⟩
    obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
    exact ⟨rs, hrs, c, hfs, (hG c a).1 ha⟩
  · rintro ⟨rs, hrs, c, hfs, ha⟩
    obtain ⟨hq, hc⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hfs⟩
    exact ⟨_, hq, c, hc, (hG c a).2 ha⟩

/-- **A write of the node at a checked path, made of the node there, is the
live write**: `delete`, `push`, `pop` and a copy over it alike. -/
theorem write_bridge {τ : State} {P : Res (Name × List Seg)} {L : Res (List Seg)}
    (hb : ∀ qs c, (L = .ok qs ∧ (SVal.struct τ.storage).findLive qs = .ok c) ↔
      ∃ rs, P = .ok rs ∧ qs = .field rs.1 :: rs.2 ∧ τ.findStorage rs.1 rs.2 = .ok c)
    (F : SVal → Res SVal) :
    Sim (L >>= fun qs => (SVal.struct τ.storage).findLive qs >>= fun c => F c >>= fun c' =>
          (SVal.struct τ.storage).saveLive qs c')
      (P >>= fun rs => τ.findStorage rs.1 rs.2 >>= fun c => F c >>= fun c' =>
          τ.saveStorage rs.1 rs.2 c' >>= fun τ' => .ok (.struct τ'.storage)) := by
  intro a
  simp only [Res.bind_eq_ok]
  constructor
  · rintro ⟨qs, hq, c, hc, c', hF, ha⟩
    obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
    rw [saveLive_eq_save _ hc, save_root] at ha
    obtain ⟨τ'', h'', he⟩ := Res.bind_eq_ok.1 ha
    exact ⟨rs, hrs, c, hfs, c', hF, τ'', h'', he⟩
  · rintro ⟨rs, hrs, c, hfs, c', hF, τ'', h'', he⟩
    obtain ⟨hq, hl⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hfs⟩
    refine ⟨_, hq, c, hl, c', hF, ?_⟩
    rw [saveLive_eq_save _ hl, save_root, h'', Res.ok_bind, he]

/-- `persons.push()` on the node: the slot appended, then written back. -/
theorem pushOn_slot (τ : State) (E : Ty) (r : Name) (segs : List Seg) (w : Value) :
    Close.pushOn τ E r segs pure =
      fun c => (AOp.slot E).apply w c >>= fun c' => τ.saveStorage r segs c' := by
  funext c
  cases c <;> rfl

/-- `values.push(w)` on the node: the word appended, then written back. -/
theorem pushOn_word (τ : State) (r : Name) (segs : List Seg) (x : Value) :
    Close.pushOn τ .uint r segs (fun _ => .ok x.toSVal) =
      fun c => AOp.push.apply x c >>= fun c' => τ.saveStorage r segs c' := by
  funext c
  cases c <;> rfl

/-- `values.pop()` on the node: the last element moved past the end, then
written back. -/
theorem popOn_pop (τ : State) (keep : Bool) (r : Name) (segs : List Seg) (w : Value) :
    Close.popOn τ keep r segs =
      fun c => (AOp.pop keep).apply w c >>= fun c' => τ.saveStorage r segs c' := by
  funext c
  cases c with
  | array elems shadow fx =>
    rcases hr : elems.reverse with _ | ⟨l, rr⟩ <;> simp only [Close.popOn, hr, AOp.apply,
        Res.ok_bind] <;> rfl
  | prim _ | struct _ | map _ _ => rfl

/-- `p = persons.push();` writes what `persons.push();` does. -/
theorem STerm.eval_extend (s : STerm C) (p : PTerm C) (E : Ty) (σ : State) :
    (STerm.extend s p E).eval σ = s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= Close.pushOn τ E rs.1 rs.2 pure := by
  simp only [Tm.eval, Op2.eval]
  cases s.eval σ with
  | error _ => rfl
  | ok τ =>
    cases p.eval σ with
    | error _ => rfl
    | ok rs =>
      simp only [Res.ok_bind, pushPlaceAt]
      cases τ.findStorage rs.1 rs.2 with
      | error _ => rfl
      | ok c =>
        cases c with
        | array elems shadow fx =>
          simp only [Res.ok_bind, Close.pushOn_array, pure, Except.pure]
          cases τ.saveStorage rs.1 rs.2 _ <;> rfl
        | prim _ | struct _ | map _ _ => rfl

/-- An empty slot copied over is the copy laid on fresh slots. -/
theorem prim_overlay (p : PrimVal) (n : SVal) : (SVal.prim p).overlay n = n.strip := by
  cases n <;> rfl

/-- A write below a location written before is one write of what is
there, written below. -/
theorem saveLive_append {new : SVal} : ∀ {v v' A : SVal} {ps : List Seg} (rest : List Seg),
    v.saveLive ps A = .ok v' →
      v'.saveLive (ps ++ rest) new = A.saveLive rest new >>= fun A' => v.saveLive ps A'
  | v, v', A, [], rest, h => by
    have : v' = A := by cases v <;> simpa only [SVal.saveLive, Except.ok.injEq] using h.symm
    subst this
    simp only [List.nil_append]
    cases v <;> cases v'.saveLive rest new <;> rfl
  | .prim _, _, _, _ :: _, _, h => by cases ‹Seg› <;> simp only [SVal.saveLive, reduceCtorEq] at h
  | .struct fields, v', A, .field f :: ps, rest, h => by
    simp only [SVal.saveLive] at h
    cases hl : lookupBy f fields with
    | none => simp only [hl, reduceCtorEq] at h
    | some old =>
      rw [hl] at h
      obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h
      cases he
      simp only [List.cons_append, SVal.saveLive, lookupBy_setBy_self, saveLive_append rest hu,
        hl, bind_assoc, setBy_setBy_self]
  | .struct _, _, _, .at _ :: _, _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .array _ _ _, _, _, .field _ :: _, _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .map _ _, _, _, .field _ :: _, _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .array elems shadow fx, v', A, .at i :: ps, rest, h => by
    simp only [SVal.saveLive] at h
    split at h
    · rename_i hi
      obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h
      cases he
      have hi' : 0 ≤ i ∧ i.toNat < (elems.set i.toNat upd).length := by
        simpa only [List.length_set] using hi
      simp only [List.cons_append, SVal.saveLive, dif_pos hi', dif_pos hi, List.get_eq_getElem,
        List.getElem_set_self, saveLive_append rest hu, bind_assoc, List.set_set]
    · cases h
  | .map entries dflt, v', A, .at i :: ps, rest, h => by
    simp only [SVal.saveLive] at h
    cases hl : lookupBy i entries with
    | none =>
      rw [hl] at h
      obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h
      cases he
      simp only [List.cons_append, SVal.saveLive, lookupBy_setBy_self, saveLive_append rest hu,
        hl, bind_assoc, setBy_setBy_self]
    | some old =>
      rw [hl] at h
      obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h
      cases he
      simp only [List.cons_append, SVal.saveLive, lookupBy_setBy_self, saveLive_append rest hu,
        hl, bind_assoc, setBy_setBy_self]


/-- Whether a write returns does not depend on what it writes. -/
theorem saveLive_other {x y : SVal} : ∀ {v u : SVal} {ps : List Seg}, v.saveLive ps x = .ok u →
    ∃ u', v.saveLive ps y = .ok u'
  | v, u, [], _ => ⟨y, by cases v <;> rfl⟩
  | .prim _, _, s :: _, h => by cases s <;> simp only [SVal.saveLive, reduceCtorEq] at h
  | .struct fields, u, .field f :: ps, h => by
    simp only [SVal.saveLive] at h ⊢
    split at h
    · rename_i old hl
      obtain ⟨upd, hu, -⟩ := Res.bind_eq_ok.1 h
      obtain ⟨u', hu'⟩ := saveLive_other (y := y) hu
      exact ⟨.struct (setBy f u' fields), by simp only [hu', Res.ok_bind]⟩
    · cases h
  | .struct _, _, .at _ :: _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .array _ _ _, _, .field _ :: _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .map _ _, _, .field _ :: _, h => by simp only [SVal.saveLive, reduceCtorEq] at h
  | .array elems shadow fx, u, .at i :: ps, h => by
    simp only [SVal.saveLive] at h ⊢
    split at h
    · rename_i hi
      obtain ⟨upd, hu, -⟩ := Res.bind_eq_ok.1 h
      obtain ⟨u', hu'⟩ := saveLive_other (y := y) hu
      simp only [List.get_eq_getElem] at hu'
      exact ⟨.array (elems.set i.toNat u') shadow fx, by simp only [hi, and_self, ↓reduceDIte,
          List.get_eq_getElem, hu', Res.ok_bind]⟩
    · cases h
  | .map entries dflt, u, .at i :: ps, h => by
    simp only [SVal.saveLive] at h ⊢
    split at h
    · rename_i old hl
      obtain ⟨upd, hu, -⟩ := Res.bind_eq_ok.1 h
      obtain ⟨u', hu'⟩ := saveLive_other (y := y) hu
      exact ⟨.map (setBy i u' entries) dflt, by simp only [hu', Res.ok_bind]⟩
    · rename_i hl
      obtain ⟨upd, hu, -⟩ := Res.bind_eq_ok.1 h
      obtain ⟨u', hu'⟩ := saveLive_other (y := y) hu
      exact ⟨.map (setBy i u' entries) dflt, by simp only [hu', Res.ok_bind]⟩

/-- Writing the slot one past the old end of a grown array. -/
theorem saveLive_last (es sh : List SVal) (fx : Bool) (x y : SVal) :
    (SVal.array (es ++ [x]) sh fx).saveLive [.at es.length] y = .ok (.array (es ++ [y]) sh fx) := by
  simp only [SVal.saveLive, Int.ofNat_zero_le, Int.toNat_natCast, List.length_append,
      List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, and_self, ↓reduceDIte,
          List.get_eq_getElem, Nat.le_refl, List.getElem_append_right, Nat.sub_self,
          List.getElem_cons_zero, List.set_append_right, List.set_cons_zero, Res.ok_bind]

theorem findLive_last (es sh : List SVal) (fx : Bool) (x : SVal) :
    (SVal.array (es ++ [x]) sh fx).findLive [.at es.length] = .ok x := by
  simp only [SVal.findLive, Int.ofNat_zero_le, Int.toNat_natCast, List.length_append,
      List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, and_self, ↓reduceDIte,
          List.get_eq_getElem, Nat.le_refl, List.getElem_append_right, Nat.sub_self,
          List.getElem_cons_zero, SVal.findLive_nil]

/-- **`tokens.push(tok)`**: a slot appended, the source copied over it. -/
theorem pushCopy_bridge {σ τ : State} {S : LStor} {P SQ : LPath}
    {PE PE' : Res (Name × List Seg)}
    (hS : S.eval σ = .ok (.struct τ.storage))
    (hb : ∀ qs c, (P.eval σ = .ok qs ∧ (SVal.struct τ.storage).findLive qs = .ok c) ↔
      ∃ rs, PE = .ok rs ∧ qs = .field rs.1 :: rs.2 ∧ τ.findStorage rs.1 rs.2 = .ok c)
    (hb' : ∀ qs c, (SQ.eval σ = .ok qs ∧ (SVal.struct τ.storage).findLive qs = .ok c) ↔
      ∃ rs, PE' = .ok rs ∧ qs = .field rs.1 :: rs.2 ∧ τ.findStorage rs.1 rs.2 = .ok c) :
    Sim ((LStor.copy (.arr (.slot .uint) S P (.lit (.bool true))) (.at P (.len S P)) S SQ).eval σ)
      (PE >>= fun rs => τ.findStorage rs.1 rs.2 >>= fun c =>
        Close.pushOn τ .uint rs.1 rs.2
          (fun _ => PE' >>= fun rs' => τ.findStorage rs'.1 rs'.2 >>= fun sv => pure sv.strip) c >>=
        fun τ' => .ok (.struct τ'.storage)) := by
  intro a
  constructor
  · intro h
    simp only [LStor.eval, LTerm.eval, LPath.eval, hS, Res.ok_bind, Res.bind_eq_ok] at h
    obtain ⟨sqs, hsq, n, hn, v', ⟨ps, hp, c, hc, c', hap, hv'⟩, qs', ⟨ps₂, hp₂, i,
      ⟨k, ⟨ps₃, hp₃, c₂, hc₂, hk⟩, hi⟩, hq'⟩, cur, hcur, ha⟩ := h
    rw [hp] at hp₂ hp₃; cases hp₂; cases hp₃
    rw [hc] at hc₂; cases hc₂
    obtain ⟨rs, hrs, rfl, hfs⟩ := (hb _ c).1 ⟨hp, hc⟩
    obtain ⟨rs', hrs', rfl, hfs'⟩ := (hb' _ n).1 ⟨hsq, hn⟩
    cases c with
    | array es sh fx =>
      simp only [AOp.apply] at hap; cases hap
      simp only [Close.arrLen] at hk; cases hk
      simp only [Value.asInt] at hi; cases hi
      cases hq'
      have hslot : (pushSlot (.prim .uint) sh).1 = .prim (.int 0) := by
        cases sh <;> simp only [pushSlot, defaultForTy, Ty.isPrimitive, ↓reduceIte] <;> rfl
      rw [SVal.findLive_append, findLive_saveLive_same hv', Res.ok_bind] at hcur
      rw [hslot, findLive_last] at hcur; cases hcur
      rw [saveLive_append _ hv', hslot, prim_overlay, saveLive_last, Res.ok_bind,
        saveLive_eq_save _ hc, save_root] at ha
      obtain ⟨τ'', h'', he⟩ := Res.bind_eq_ok.1 ha
      simp only [hrs, Res.ok_bind, hfs, Close.pushOn_array, hrs', hfs', pure, Except.pure]
      rw [h'']
      exact he
    | prim _ | struct _ | map _ _ => simp only [AOp.apply, reduceCtorEq] at hap
  · intro h
    obtain ⟨rs, hrs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨c, hfs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨τ'', h, he⟩ := Res.bind_eq_ok.1 h
    cases c with
    | array es sh fx =>
      simp only [Close.pushOn_array] at h
      obtain ⟨n', hval, h⟩ := Res.bind_eq_ok.1 h
      obtain ⟨rs', hrs', hval⟩ := Res.bind_eq_ok.1 hval
      obtain ⟨n, hfs', hval⟩ := Res.bind_eq_ok.1 hval
      simp only [pure, Except.pure, Except.ok.injEq] at hval; subst hval
      obtain ⟨hp, hc⟩ := (hb _ _).2 ⟨rs, hrs, rfl, hfs⟩
      obtain ⟨hsq, hn⟩ := (hb' _ _).2 ⟨rs', hrs', rfl, hfs'⟩
      have hslot : (pushSlot (.prim .uint) sh).1 = .prim (.int 0) := by
        cases sh <;> simp only [pushSlot, defaultForTy, Ty.isPrimitive, ↓reduceIte] <;> rfl
      have hsv : (SVal.struct τ.storage).saveLive (.field rs.1 :: rs.2)
          (.array (es ++ [n.strip]) (pushSlot .uint sh).2 fx) = .ok a := by
        rw [saveLive_eq_save _ hc, save_root, h, Res.ok_bind, he]
      obtain ⟨v', hv'⟩ := saveLive_other (y := .array (es ++ [(pushSlot .uint sh).1])
        (pushSlot .uint sh).2 fx) hsv
      simp only [LStor.eval, LTerm.eval, LPath.eval, hS, Res.ok_bind, Res.bind_eq_ok]
      refine ⟨_, hsq, n, hn, v', ⟨_, hp, _, hc, _, rfl, hv'⟩, _, ⟨_, hp, _,
        ⟨_, ⟨_, hp, _, hc, rfl⟩, rfl⟩, rfl⟩, (pushSlot .uint sh).1, ?_, ?_⟩
      · rw [SVal.findLive_append, findLive_saveLive_same hv', Res.ok_bind, findLive_last]
      · rw [saveLive_append _ hv', hslot, prim_overlay, saveLive_last, Res.ok_bind]
        exact hsv
    | prim _ | struct _ | map _ _ => simp only [Close.pushOn, reduceCtorEq] at h

/-- A write to the storage keeps what the names hold, an alias through an
index made stale. -/
theorem lookupBy_onWrite (y : Var) : ∀ (env : List (Var × SymB)),
    lookupBy y (env.map fun b => (b.1, b.2.onWrite)) = (lookupBy y env).map SymB.onWrite
  | [] => rfl
  | (x, b) :: rest => by
    by_cases hy : y = x <;> simp only [hy, List.map_cons, lookupBy, ↓reduceIte, Option.map_some,
        lookupBy_onWrite y rest]

/-- A write to the storage keeps the relation of each name. -/
theorem EnvRel.onWrite {σ τ τ' : State} {y : Var} {o : Option SymB}
    (h : EnvRel σ τ y o) (he : τ'.getEnv y = τ.getEnv y) : EnvRel σ τ' y (o.map SymB.onWrite) := by
  rcases o with _ | ⟨t⟩ | ⟨q⟩ | _ | ⟨s⟩ | ⟨k⟩
  · simp only [EnvRel, Option.map] at h ⊢; rw [he]; exact h
  · simp only [EnvRel, Option.map, SymB.onWrite] at h ⊢; rw [he]; exact h
  · simp only [EnvRel] at h
    obtain ⟨r, segs, h₁, h₂, -⟩ := h
    by_cases hn : q.noAt = true
    · simp only [Option.map, SymB.onWrite, hn, if_true, EnvRel]
      exact ⟨r, segs, h₁, by rw [he]; exact h₂, LiveTo.of_noAt _ (LPath.noAt_eval σ hn h₁)⟩
    · simp only [Option.map, SymB.onWrite, hn, if_false, EnvRel, Bool.false_eq_true]
      exact ⟨r, segs, by rw [he]; exact h₂⟩
  · simp only [EnvRel, Option.map, SymB.onWrite] at h ⊢; rw [he]; exact h
  · simp only [EnvRel, Option.map, SymB.onWrite] at h ⊢; rw [he]; exact h
  · simp only [EnvRel, Option.map, SymB.onWrite] at h ⊢; rw [he]; exact h

/-! ### Memory, symbolically and concretely

A read of an object the updates allocated is the term its slot holds
(`readL_sim`), a write the object the interpreter writes (`writeL_rel`),
each with the guard that returns exactly where the interpreter's operation
does. -/

/-- A ground term returns its value in every state. -/
theorem LTerm.ground?_eval (σ : State) : (t : LTerm) → ∀ {v : Value}, t.ground? = some v →
    t.eval σ = .ok v
  | .lit _, v, h => by
    simp only [LTerm.ground?, Option.some.injEq] at h
    subst h; rfl
  | .binop op p a b, v, h => by
    simp only [LTerm.ground?] at h
    split at h
    · rename_i x y ha hb
      split at h
      · rename_i r hr
        simp only [Option.some.injEq] at h
        subst h
        simp only [LTerm.eval, LTerm.ground?_eval σ a ha, LTerm.ground?_eval σ b hb, Res.ok_bind,
          hr]
      · cases h
    · cases h
  | .unop op p a, v, h => by
    simp only [LTerm.ground?] at h
    split at h
    · rename_i x ha
      split at h
      · rename_i r hr
        simp only [Option.some.injEq] at h
        subst h
        simp only [LTerm.eval, LTerm.ground?_eval σ a ha, Res.ok_bind, hr]
      · cases h
    · cases h
  | .var _, _, h | .ite .., _, h | .find .., _, h | .has .., _, h | .kmap .., _, h
  | .len .., _, h | .sok _, _, h | .pok _, _, h | .seq .., _, h | .orElse .., _, h
  | .kite .., _, h | .zero _, _, h | .err, _, h | .env _, _, h | .findP .., _, h => by
    simp only [LTerm.ground?, reduceCtorEq] at h

theorem seqL_eval (σ : State) (g a : LTerm) :
    (seqL g a).eval σ = g.eval σ >>= fun _ => a.eval σ := by
  unfold seqL; split <;> rfl

/-- The guard of an index returns exactly where the index is an integer. -/
theorem isIntL_ret (σ : State) (t : LTerm) :
    (∃ v, (isIntL t).eval σ = .ok v) ↔ ∃ i, t.eval σ = .ok (.int i) := by
  unfold isIntL
  split
  · rename_i i hi
    exact ⟨fun _ => ⟨i, LTerm.ground?_eval σ t hi⟩, fun _ => ⟨_, rfl⟩⟩
  · constructor
    · rintro ⟨v, hv⟩
      simp only [LTerm.eval] at hv
      cases ht : t.eval σ with
      | error e => rw [ht] at hv; cases hv
      | ok w =>
        cases w with
        | int i => exact ⟨i, rfl⟩
        | bool b => rw [ht] at hv; cases hv
    · rintro ⟨i, hi⟩
      exact ⟨.bool true, by simp only [LTerm.eval, hi, Res.ok_bind, Value.asInt, ite_self]⟩

/-- The case split on an index: the slot at it, read where it is one. -/
theorem kchainL_eval (σ : State) {t : LTerm} {i : Int} (ht : t.eval σ = .ok (.int i)) :
    (es : List (SMV LTerm)) → (j : Nat) → (kchainL t j es).eval σ =
      if (j : Int) ≤ i then
        (match es[(i - j).toNat]? with
          | some e => (slotT e).eval σ
          | none => .error .stuck)
      else .error .stuck
  | [], j => by
    simp only [kchainL, LTerm.eval, List.getElem?_nil, ite_self]
  | e :: es, j => by
    simp only [kchainL, LTerm.eval, ht, Res.ok_bind, Value.asInt]
    by_cases hij : i = (j : Int)
    · subst hij
      simp only [if_true, if_pos (Int.le_refl _), Int.sub_self, Int.toNat_zero,
        List.getElem?_cons_zero]
    · rw [if_neg hij, kchainL_eval σ ht es (j + 1)]
      by_cases hle : (j : Int) ≤ i
      · have hn : (i - j).toNat = (i - (j + 1 : Nat)).toNat + 1 := by omega
        have hle' : ((j + 1 : Nat) : Int) ≤ i := by omega
        rw [if_pos hle, if_pos hle', hn, List.getElem?_cons_succ]
      · have hle' : ¬ ((j + 1 : Nat) : Int) ≤ i := by omega
        rw [if_neg hle, if_neg hle']

/-- A slot read as a word, on both sides. -/
theorem slotT_sim (σ : State) (b : Nat) :
    (e : SMV LTerm) → e.Ok (fun t => t.eval σ) →
      Sim ((slotT e).eval σ) ((e.conc (fun t => t.eval σ) b).asValue)
  | .val t, ⟨v, hv⟩ => Sim.of_eq (by
    simp only [slotT, SMV.conc_val hv, hv, Close.asValue_toMVal])
  | .ref _, _ => Sim.of_eq rfl

/-- What an address the updates' objects resolve to: the member of the
`k`-th object, or its element at the integer the index term returns. -/
def AddrOf (σ : State) (k : Nat) : MSel → Addr → Prop
  | .fld f, ad => ad = .memoryField (σ.nextId + k) f
  | .idx t, ad => ∃ i, t.eval σ = .ok (.int i) ∧ ad = .memoryIndex (σ.nextId + k) i

theorem getElem?_some_lt {β : Type} {l : List β} {k : Nat} {o : β} (h : l[k]? = some o) :
    ∃ hk : k < l.length, l[k] = o := by
  rw [List.getElem?_eq_some_iff] at h
  exact h

/-- **A read, symbolically and concretely.** -/
theorem readL_sim {σ μ : State} {M : SMem LTerm}
    (hM : MemRel (fun t => t.eval σ) σ.nextId M μ) {k : Nat} {sel : MSel} {r : LTerm}
    (hr : readL M k sel = some r) {ad : Addr} (ha : AddrOf σ k sel ad) :
    Sim (r.eval σ) (readAddr μ ad >>= MVal.asValue) := by
  unfold readL at hr
  cases hk : M[k]? with
  | none => simp only [hk, reduceCtorEq] at hr
  | some o =>
    obtain ⟨hlt, hget⟩ := getElem?_some_lt hk
    have hobj := hM.obj k hlt
    have hok := hM.ok o (hget ▸ List.getElem_mem hlt)
    rw [hget] at hobj
    cases o with
    | struct fs =>
      cases sel with
      | fld f =>
        simp only [hk, Option.some.injEq] at hr
        subst hr
        simp only [AddrOf] at ha
        subst ha
        simp only [readAddr, hobj, SObj.conc, bind, Except.bind, lookupBy_map_conc]
        cases hl : lookupBy f fs with
        | none => exact Sim.of_eq rfl
        | some e => exact slotT_sim σ _ e (hok _ (lookupBy_mem_name fs hl))
      | idx t =>
        simp only [hk, Option.some.injEq] at hr
        subst hr
        obtain ⟨i, -, rfl⟩ := ha
        simp only [readAddr, hobj, SObj.conc, bind, Except.bind]
        exact Sim.of_eq rfl
    | array es fx =>
      cases sel with
      | fld f =>
        simp only [hk, Option.some.injEq] at hr
        subst hr
        simp only [AddrOf] at ha
        subst ha
        simp only [readAddr, hobj, SObj.conc, bind, Except.bind]
        exact Sim.of_eq rfl
      | idx t =>
        simp only [hk, Option.some.injEq] at hr
        subst hr
        obtain ⟨i, hti, rfl⟩ := ha
        have hconc : readAddr μ (.memoryIndex (σ.nextId + k) i) >>= MVal.asValue =
            if h : 0 ≤ i ∧ i.toNat < es.length then
              (es[i.toNat].conc (fun t => t.eval σ) σ.nextId).asValue
            else .error .revert := by
          by_cases hc : 0 ≤ i ∧ i.toNat < es.length
          · have hc' : 0 ≤ i ∧ i.toNat < (es.map (SMV.conc (fun t => t.eval σ) σ.nextId)).length := by
              simpa only [List.length_map] using hc
            simp only [readAddr, hobj, SObj.conc, bind, Except.bind, dif_pos hc', dif_pos hc, pure,
              Except.pure, List.get_eq_getElem, List.getElem_map]
          · have hc' : ¬ (0 ≤ i ∧
                i.toNat < (es.map (SMV.conc (fun t => t.eval σ) σ.nextId)).length) := by
              simpa only [List.length_map] using hc
            simp only [readAddr, hobj, SObj.conc, bind, Except.bind, dif_neg hc', dif_neg hc]
        rw [hconc]
        have hes : ∀ e ∈ es, e.Ok (fun t => t.eval σ) := hok
        split
        · rename_i i' hi'
          rw [LTerm.ground?_eval σ t hi', Except.ok.injEq, PrimVal.int.injEq] at hti
          subst hti
          split
          · exact slotT_sim σ _ _ (hes _ (List.getElem_mem _))
          · exact Sim.halt (fun _ h => nomatch h) (fun _ h => nomatch h)
        · rw [kchainL_eval σ hti es 0]
          have h0 : ((0 : Nat) : Int) = 0 := rfl
          simp only [h0, Int.sub_zero]
          by_cases hc : 0 ≤ i ∧ i.toNat < es.length
          · rw [if_pos hc.1, List.getElem?_eq_getElem hc.2, dif_pos hc]
            exact slotT_sim σ _ _ (hes _ (List.getElem_mem _))
          · rw [dif_neg hc]
            refine Sim.halt (fun a ha => ?_) (fun a ha => nomatch ha)
            by_cases h1 : 0 ≤ i
            · rw [if_pos h1, List.getElem?_eq_none (by omega)] at ha
              simp only [reduceCtorEq] at ha
            · rw [if_neg h1] at ha
              simp only [reduceCtorEq] at ha

/-- `xs.length` of an allocated object, on both sides. -/
theorem mlenL_sim {σ μ : State} {M : SMem LTerm}
    (hM : MemRel (fun t => t.eval σ) σ.nextId M μ) {k : Nat} {r : LTerm}
    (hr : mlenL M k = some r) : Sim (r.eval σ) (memArrayLen μ (σ.nextId + k)) := by
  unfold mlenL at hr
  cases hk : M[k]? with
  | none => simp only [hk, reduceCtorEq] at hr
  | some o =>
    obtain ⟨hlt, hget⟩ := getElem?_some_lt hk
    have hobj := hM.obj k hlt
    rw [hget] at hobj
    cases o with
    | struct fs =>
      simp only [hk, Option.some.injEq] at hr
      subst hr
      simp only [memArrayLen, hobj, SObj.conc, bind, Except.bind]
      exact Sim.of_eq rfl
    | array es fx =>
      simp only [hk, Option.some.injEq] at hr
      subst hr
      simp only [memArrayLen, hobj, SObj.conc, bind, Except.bind, List.length_map]
      exact Sim.of_eq rfl

/-- A reference read out of an allocated object, on both sides. -/
theorem ireadL_eq {σ μ : State} {M : SMem LTerm}
    (hM : MemRel (fun t => t.eval σ) σ.nextId M μ) {k k' : Nat} {sel : MSel}
    (hr : ireadL M k sel = some k') {ad : Addr} (ha : AddrOf σ k sel ad) :
    readAddr μ ad >>= MVal.asRef = .ok (σ.nextId + k') := by
  unfold ireadL at hr
  cases hk : M[k]? with
  | none => simp only [hk, reduceCtorEq] at hr
  | some o =>
    obtain ⟨hlt, hget⟩ := getElem?_some_lt hk
    have hobj := hM.obj k hlt
    rw [hget] at hobj
    cases o with
    | struct fs =>
      cases sel with
      | fld f =>
        simp only [hk] at hr
        simp only [AddrOf] at ha
        subst ha
        split at hr
        · rename_i k₁ hl
          simp only [Option.some.injEq] at hr
          subst hr
          simp only [readAddr, hobj, SObj.conc, bind, Except.bind]
          rw [lookupBy_map_conc, hl]
          rfl
        · cases hr
      | idx t => simp only [hk, reduceCtorEq] at hr
    | array es fx =>
      cases sel with
      | fld f => simp only [hk, reduceCtorEq] at hr
      | idx t =>
        simp only [hk] at hr
        obtain ⟨i, hti, rfl⟩ := ha
        split at hr
        · rename_i i' hi'
          rw [LTerm.ground?_eval σ t hi', Except.ok.injEq, PrimVal.int.injEq] at hti
          subst hti
          split at hr
          · rename_i hin
            split at hr
            · rename_i k₁ he
              simp only [Option.some.injEq] at hr
              subst hr
              have hin' : 0 ≤ i' ∧ i'.toNat < (es.map (SMV.conc (fun t => t.eval σ) σ.nextId)).length := by
                simpa only [List.length_map] using hin
              simp only [readAddr, hobj, SObj.conc, bind, Except.bind, dif_pos hin', pure,
                Except.pure]
              simp only [List.get_eq_getElem, List.getElem_map, he]
              rfl
            · cases hr
          · cases hr
        · cases hr

/-- The elements after a word written at an index that is no literal. -/
theorem kwriteL_conc {σ : State} {b : Nat} {t u : LTerm} {es : List (SMV LTerm)}
    (hval : es.all SMV.isVal = true) (hes : ∀ e ∈ es, e.Ok (fun t => t.eval σ))
    {i : Int} (hti : t.eval σ = .ok (.int i)) (hi0 : 0 ≤ i) {w : Value} (hu : u.eval σ = .ok w) :
    (kwriteL t u es).map (SMV.conc (fun t => t.eval σ) b) =
      (es.map (SMV.conc (fun t => t.eval σ) b)).set i.toNat w.toMVal ∧
    ∀ s ∈ kwriteL t u es, s.Ok (fun t => t.eval σ) := by
  have helem : ∀ (j : Nat) (hj : j < es.length), ∃ v,
      (LTerm.kite t (.lit (.int j)) u (slotT es[j])).eval σ = .ok v ∧
      v.toMVal = if i.toNat = j then w.toMVal else es[j].conc (fun t => t.eval σ) b := by
    intro j hj
    have hv : es[j].isVal = true := List.all_eq_true.1 hval _ (List.getElem_mem hj)
    obtain ⟨v', hv'⟩ : ∃ v', (slotT es[j]).eval σ = .ok v' ∧
        es[j].conc (fun t => t.eval σ) b = v'.toMVal := by
      have hok := hes _ (List.getElem_mem hj)
      revert hv hok
      cases es[j] with
      | val t' =>
        intro _ hok
        obtain ⟨v', h'⟩ := hok
        exact ⟨v', h', SMV.conc_val h'⟩
      | ref _ => intro hv; simp only [SMV.isVal, Bool.false_eq_true] at hv
    simp only [LTerm.eval, hti, Res.ok_bind, Value.asInt]
    by_cases hij : i = (j : Int)
    · rw [if_pos hij]
      exact ⟨w, hu, by rw [if_pos (by omega)]⟩
    · rw [if_neg hij]
      exact ⟨v', hv'.1, by rw [if_neg (by omega), hv'.2]⟩
  constructor
  · apply List.ext_getElem
    · simp only [kwriteL, List.length_map, List.length_mapIdx, List.length_set]
    · intro j h1 h2
      have hj : j < es.length := by simpa only [List.length_set, List.length_map] using h2
      obtain ⟨v, hv, hc⟩ := helem j hj
      simp only [kwriteL, List.getElem_map, List.getElem_mapIdx, List.getElem_set]
      rw [SMV.conc_val hv, hc]
  · intro s hs
    simp only [kwriteL, List.mem_mapIdx] at hs
    obtain ⟨j, hj, rfl⟩ := hs
    obtain ⟨v, hv, -⟩ := helem j hj
    exact ⟨v, hv⟩

/-- The guard of a write at an index that is no literal returns where it is in range. -/
theorem kchainL_true {σ : State} {t : LTerm} {i : Int} (hti : t.eval σ = .ok (.int i))
    (es : List (SMV LTerm)) :
    (∃ v, (kchainL t 0 (es.map fun _ => .val (.lit (.bool true)))).eval σ = .ok v) ↔
      (0 ≤ i ∧ i.toNat < es.length) := by
  rw [kchainL_eval σ hti]
  have h0 : ((0 : Nat) : Int) = 0 := rfl
  simp only [h0, Int.sub_zero]
  by_cases h1 : 0 ≤ i
  · rw [if_pos h1]
    by_cases h2 : i.toNat < es.length
    · rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using h2)]
      simp only [List.getElem_map, slotT, LTerm.eval]
      exact ⟨fun _ => ⟨h1, h2⟩, fun _ => ⟨_, rfl⟩⟩
    · rw [List.getElem?_eq_none (by simp only [List.length_map]; omega)]
      simp only [reduceCtorEq, exists_false, false_iff]
      omega
  · rw [if_neg h1]
    simp only [reduceCtorEq, exists_false, false_iff]
    omega

/-- **A write, symbolically and concretely.** -/
theorem writeL_rel {σ μ : State} {M M' : SMem LTerm}
    (hM : MemRel (fun t => t.eval σ) σ.nextId M μ) {k : Nat} {sel : MSel} {s : SMV LTerm}
    {gw : LTerm} (hw : writeL M k sel s = some (M', gw)) (hs : s.Ok (fun t => t.eval σ))
    {ad : Addr} (ha : AddrOf σ k sel ad) :
    ((∃ v, gw.eval σ = .ok v) ↔ ∃ μ', writeAddr μ (s.conc (fun t => t.eval σ) σ.nextId) ad = .ok μ') ∧
    ∀ μ', writeAddr μ (s.conc (fun t => t.eval σ) σ.nextId) ad = .ok μ' →
      MemRel (fun t => t.eval σ) σ.nextId M' μ' := by
  unfold writeL at hw
  cases hk : M[k]? with
  | none => simp only [hk, reduceCtorEq] at hw
  | some o =>
    obtain ⟨hlt, hget⟩ := getElem?_some_lt hk
    have hobj := hM.obj k hlt
    have hok := hM.ok o (hget ▸ List.getElem_mem hlt)
    rw [hget] at hobj
    cases o with
    | struct fs =>
      cases sel with
      | fld f =>
        simp only [hk, Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [AddrOf] at ha
        subst ha
        obtain ⟨hw1, hrel⟩ := hM.writeField hlt hget f hs
        refine ⟨⟨fun _ => ⟨_, by simp only [writeAddr]; exact hw1⟩, fun _ => ⟨_, rfl⟩⟩, fun μ' hμ' => ?_⟩
        simp only [writeAddr, hw1, Except.ok.injEq] at hμ'
        subst hμ'
        exact hrel
      | idx t =>
        simp only [hk, Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        obtain ⟨i, -, rfl⟩ := ha
        have hbad : ∀ μ', writeAddr μ (s.conc (fun t => t.eval σ) σ.nextId)
            (.memoryIndex (σ.nextId + k) i) ≠ .ok μ' := by
          intro μ' h'
          simp only [writeAddr, memWriteIndex, hobj, SObj.conc, bind, Except.bind,
            reduceCtorEq] at h'
        exact ⟨⟨(fun ⟨_, h'⟩ => nomatch h'), fun ⟨μ', h'⟩ => absurd h' (hbad μ')⟩,
          fun μ' h' => absurd h' (hbad μ')⟩
    | array es fx =>
      cases sel with
      | fld f =>
        simp only [hk, Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [AddrOf] at ha
        subst ha
        have hbad : ∀ μ', writeAddr μ (s.conc (fun t => t.eval σ) σ.nextId)
            (.memoryField (σ.nextId + k) f) ≠ .ok μ' := by
          intro μ' h'
          simp only [writeAddr, memWriteField, hobj, SObj.conc, bind, Except.bind,
            reduceCtorEq] at h'
        exact ⟨⟨(fun ⟨_, h'⟩ => nomatch h'), fun ⟨μ', h'⟩ => absurd h' (hbad μ')⟩,
          fun μ' h' => absurd h' (hbad μ')⟩
      | idx t =>
        obtain ⟨i, hti, rfl⟩ := ha
        simp only [hk] at hw
        split at hw
        · rename_i i' hi'
          rw [LTerm.ground?_eval σ t hi', Except.ok.injEq, PrimVal.int.injEq] at hti
          subst hti
          split at hw
          · rename_i hin
            simp only [Option.some.injEq, Prod.mk.injEq] at hw
            obtain ⟨rfl, rfl⟩ := hw
            obtain ⟨hw1, hrel⟩ := hM.writeIndex hlt hget hin hs
            refine ⟨⟨fun _ => ⟨_, by simp only [writeAddr]; exact hw1⟩, fun _ => ⟨_, rfl⟩⟩,
              fun μ' hμ' => ?_⟩
            simp only [writeAddr, hw1, Except.ok.injEq] at hμ'
            subst hμ'
            exact hrel
          · rename_i hin
            simp only [Option.some.injEq, Prod.mk.injEq] at hw
            obtain ⟨rfl, rfl⟩ := hw
            have hbad := hM.writeIndex_out hlt hget hin (s.conc (fun t => t.eval σ) σ.nextId)
            refine ⟨⟨(fun ⟨_, h'⟩ => nomatch h'), fun ⟨μ', h'⟩ => ?_⟩, fun μ' h' => ?_⟩ <;>
              simp only [writeAddr, hbad, reduceCtorEq] at h'
        · rename_i hng
          split at hw
          · rename_i u
            split at hw
            · rename_i hval
              simp only [Option.some.injEq, Prod.mk.injEq] at hw
              obtain ⟨rfl, rfl⟩ := hw
              obtain ⟨w, hu⟩ := hs
              have hes : ∀ e ∈ es, e.Ok (fun t => t.eval σ) := hok
              rw [kchainL_true hti es, SMV.conc_val hu]
              by_cases hin : 0 ≤ i ∧ i.toNat < es.length
              · obtain ⟨hc, hko⟩ := kwriteL_conc (b := σ.nextId) hval hes hti hin.1 hu
                have hin' : 0 ≤ i ∧ i.toNat < (es.map (SMV.conc (fun t => t.eval σ) σ.nextId)).length := by
                  simpa only [List.length_map] using hin
                have hw1 : writeAddr μ w.toMVal (.memoryIndex (σ.nextId + k) i) =
                    .ok (μ.setObj (σ.nextId + k) ((SObj.array (kwriteL t u es) fx).conc
                      (fun t => t.eval σ) σ.nextId)) := by
                  simp only [writeAddr, memWriteIndex, hobj, SObj.conc, bind, Except.bind, if_pos hin', hc]
                refine ⟨⟨fun _ => ⟨_, hw1⟩, fun _ => hin⟩, fun μ' hμ' => ?_⟩
                rw [hw1, Except.ok.injEq] at hμ'
                subst hμ'
                exact hM.set hlt _ hko
              · have hbad := hM.writeIndex_out hlt hget hin w.toMVal
                refine ⟨⟨fun h' => absurd h' hin, fun ⟨μ', h'⟩ => ?_⟩, fun μ' h' => ?_⟩ <;>
                  simp only [writeAddr, hbad, reduceCtorEq] at h'
            · cases hw
          · cases hw

/-- The symbols of a term, the measure the proofs below recurse on. -/
def _root_.Solidity.Tm.lsize : Tm C s → Nat
  | .app1 _ a => a.lsize + 1
  | .app2 _ a b => a.lsize + b.lsize + 1
  | .app3 _ a b c => a.lsize + b.lsize + c.lsize + 1
  | .pvV _ | .pvP _ | .pvS _ | .pvI _ | .app0 _ => 0

/-- `x.lsize < n` for a direct subterm `x` of a term of size below `n + 1`. -/
macro "lsize_tac" : tactic => `(tactic| (simp only [Solidity.Tm.lsize] at *; omega))

/-! The statements below, one per sort, for the terms of fewer than `n`
symbols: each sort's step is its own declaration, proved from the others at
`n` (`Rel.all_ok` puts them together by induction on `n`). -/

/-- A value term reads, pushed in, what it read after the updates. -/
def TermOK (C : Contract) (σ τ : State) (ρ : Sym) (n : Nat) : Prop :=
  ∀ t : Term C, t.lsize < n → t.inL ρ = true → Sim ((t.toL ρ).eval σ) (t.eval τ)

/-- A path, pushed in, is the path the program took, checked. -/
def PathOK (C : Contract) (σ τ : State) (ρ : Sym) (n : Nat) : Prop :=
  ∀ p : PTerm C, p.lsize < n → p.inL ρ = true → ∀ (qs : List Seg),
    (∃ rs, p.eval τ = .ok rs ∧ qs = .field rs.1 :: rs.2) ↔
      ((p.toL ρ).eval σ = .ok qs ∧ LiveTo (.struct τ.storage) qs)

/-- An identity, pushed in, is the offset of the object it names. -/
def IdOK (C : Contract) (σ τ : State) (ρ : Sym) (n : Nat) : Prop :=
  ∀ i : ITerm C, i.lsize < n → i.inL ρ = true → ∃ k g, i.toL ρ = some (k, g) ∧
    ∀ id, i.eval τ = .ok id ↔ (id = σ.nextId + k ∧ ∃ v, g.eval σ = .ok v)

/-- An address, pushed in, is the object and what selects in it. -/
def AddrOK (C : Contract) (σ τ : State) (ρ : Sym) (n : Nat) : Prop :=
  ∀ a : MAddr C, a.lsize < n → a.inL ρ = true → ∃ k sel g, a.toL ρ = some (k, sel, g) ∧
    ((∃ v, g.eval σ = .ok v) → ∃ ad, a.eval τ = .ok ad) ∧
    ∀ ad, a.eval τ = .ok ad → (∃ v, g.eval σ = .ok v) ∧ AddrOf σ k sel ad

/-- A memory, pushed in, is the objects after it. -/
def MemOK (C : Contract) (σ τ : State) (ρ : Sym) (n : Nat) : Prop :=
  ∀ m : MTerm C, m.lsize < n → m.inL ρ = true → ∃ M g, m.toL ρ = some (M, g) ∧
    ((∃ v, g.eval σ = .ok v) → ∃ μ, m.eval τ = .ok μ) ∧
    ∀ μ, m.eval τ = .ok μ → (∃ v, g.eval σ = .ok v) ∧ MemRel (fun t => t.eval σ) σ.nextId M μ

/-- A memory value, pushed in, is the slot it writes. -/
def MValOK (C : Contract) (σ τ : State) (ρ : Sym) (n : Nat) : Prop :=
  ∀ v : MValT C, v.lsize < n → v.inL ρ = true → ∃ s g, v.toL ρ = some (s, g) ∧
    ((∃ w, g.eval σ = .ok w) → s.Ok (fun t => t.eval σ)) ∧
    ∀ mv, v.eval τ = .ok mv ↔ ((∃ w, g.eval σ = .ok w) ∧ s.Ok (fun t => t.eval σ) ∧
      mv = s.conc (fun t => t.eval σ) σ.nextId)

section
variable {σ τ : State} {ρ : Sym}

/-- **A term reads, pushed in, what it read after the updates.**  Example:
after `balances[k] = 5;`, the local `y` of `uint y = balances[k];` is the
term `find(save(storage, balances[k], 5), balances[k])`, read in the state
before the write. -/
theorem Term.toL_step (h : Rel σ ρ τ) {n : Nat}
    (hT : TermOK C σ τ ρ n) (hP : PathOK C σ τ ρ n) (hI : IdOK C σ τ ρ n)
    (hA : AddrOK C σ τ ρ n) (hM : MemOK C σ τ ρ n) (_hV : MValOK C σ τ ρ n) :
    TermOK C σ τ ρ (n + 1) := fun t hn hf => match t, hn, hf with
  | .lit _, hn, _ => Sim.refl _
  | .env k, hn, _ => by
    rw [Close.Term.eval_env, h.tx k]
    exact Sim.refl _
  | .pv x, hn, _ => by
    have hx := h.env x
    rw [Close.Term.eval_pv]
    apply Sim.of_eq
    rcases hl : lookupBy x ρ.env with _ | ⟨t⟩ | ⟨q⟩ | _ | ⟨S⟩ | ⟨k⟩ <;> rw [hl] at hx <;>
      simp only [EnvRel] at hx <;> simp only [Tm.toL, hl]
    · rw [hx]; rfl
    · obtain ⟨v, h₁, h₂⟩ := hx; rw [h₁, h₂]; rfl
    · obtain ⟨r, segs, _, h₂, _⟩ := hx; rw [h₂]; rfl
    · obtain ⟨r, segs, h₂⟩ := hx; rw [h₂]; rfl
    · obtain ⟨st, -, h₂⟩ := hx; rw [h₂]; rfl
    · rw [hx]; rfl
  | .binop op p a b, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    rw [Close.Term.eval_binop]
    simp only [Tm.toL, Op2.toLAt, Op2.toL, LTerm.eval]
    exact Sim.bind (hT a (by lsize_tac) hf.1) fun _ => evalBinop_sim (hT b (by lsize_tac) hf.2)
  | .unop op p a, hn, hf => by
    simp only [Tm.inL, Op1.inL] at hf
    rw [Close.Term.eval_unop]
    simp only [Tm.toL, Op1.toL, LTerm.eval]
    exact Sim.bind (hT a (by lsize_tac) hf) fun _ => Sim.refl _
  | .find s p, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true, Bool.or_eq_true] at hf
    obtain ⟨hs | hs, hf⟩ := hf
    · obtain rfl := STerm.isStorage_eq hs
      have hb := live_bridge (hP p (by lsize_tac) hf)
      rw [Close.Term.eval_find]
      simp only [Tm.toL, Tm.storLocal?, Op2.toLAt, Op0.toL, LTerm.eval, h.stor, Res.ok_bind]
      intro a
      simp only [Res.bind_eq_ok, Close.STerm.eval_storage, Res.ok_bind]
      constructor
      · rintro ⟨qs, hq, c, hc, ha⟩
        obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
        exact ⟨rs, hrs, c, hfs, ha⟩
      · rintro ⟨rs, hrs, c, hfs, ha⟩
        obtain ⟨hq, hc⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hfs⟩
        exact ⟨_, hq, c, hc, ha⟩
    · -- `find(old, p)`: the path checked against the storage the updates left,
      -- the snapshot read there
      obtain ⟨x, S, rfl, hl⟩ := Tm.storLocal?_isSome hs
      have hx := h.env x
      rw [hl] at hx
      obtain ⟨st, hS, hst⟩ := hx
      have hA := hP p (by lsize_tac) hf
      have hg := guardPath_ok h.stor (p.toL ρ)
      rw [Close.Term.eval_find, Close.STerm.eval_pv, hst]
      simp only [Tm.toL, Tm.storLocal?, hl, Op2.toLAt, LTerm.eval, hS, Res.ok_bind,
        Close.bindingStore_store]
      intro a
      constructor
      · intro H
        obtain ⟨g, hgv, H⟩ := Res.bind_eq_ok.1 H
        obtain ⟨qs, hq, hlive⟩ := hg.1 ⟨g, hgv⟩
        obtain ⟨rs, hrs, rfl⟩ := (hA _).2 ⟨hq, hlive⟩
        rw [hq, Res.ok_bind] at H
        rw [hrs, Res.ok_bind, ← find_root]
        exact H
      · intro H
        obtain ⟨rs, hrs, H⟩ := Res.bind_eq_ok.1 H
        obtain ⟨hq, hlive⟩ := (hA _).1 ⟨rs, hrs, rfl⟩
        obtain ⟨g, hgv⟩ := hg.2 ⟨_, hq, hlive⟩
        rw [hgv, Res.ok_bind, hq, Res.ok_bind]
        rw [← find_root] at H
        exact H
  | .len s p, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨hs, hf⟩ := hf
    obtain rfl := STerm.isStorage_eq hs
    have hb := live_bridge (hP p (by lsize_tac) hf)
    rw [Close.Term.eval_len]
    simp only [Tm.toL, Op0.toL, Op2.toLAt, Op2.toL, LTerm.eval, h.stor, Res.ok_bind]
    intro a
    simp only [Res.bind_eq_ok, Close.STerm.eval_storage, Res.ok_bind]
    constructor
    · rintro ⟨qs, hq, c, hc, ha⟩
      obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
      exact ⟨rs, hrs, c, hfs, ha⟩
    · rintro ⟨rs, hrs, c, hfs, ha⟩
      obtain ⟨hq, hc⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hfs⟩
      exact ⟨_, hq, c, hc, ha⟩
  | .ite c a b, hn, hf => by
    simp only [Tm.inL, Op3.inL, Bool.and_eq_true] at hf
    rw [Close.Term.eval_ite]
    simp only [Tm.toL, Op3.toL, LTerm.eval]
    exact Sim.bind (hT c (by lsize_tac) hf.1.1) fun _ =>
      pickBranch_sim (hT a (by lsize_tac) hf.1.2) (hT b (by lsize_tac) hf.2)
  | .read m a, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨⟨hm, ha⟩, hr⟩ := hf
    obtain ⟨M, g, hM, hmr, hme⟩ := hM m (by lsize_tac) hm
    obtain ⟨k, sel, g', hA, har, hae⟩ := hA a (by lsize_tac) ha
    simp only [hM, hA, readOk] at hr
    obtain ⟨r, hrr⟩ := Option.isSome_iff_exists.1 hr
    simp only [Tm.toL, Op2.toLAt, Op2.toL, hM, hA, hrr]
    rw [Close.Term.eval_read]
    intro w
    rw [seqL_eval, seqL_eval]
    constructor
    · intro hw
      obtain ⟨_, hg, hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨_, hg', hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨μ, hμ⟩ := hmr ⟨_, hg⟩
      obtain ⟨-, hrel⟩ := hme μ hμ
      obtain ⟨ad, had⟩ := har ⟨_, hg'⟩
      obtain ⟨-, hao⟩ := hae ad had
      rw [hμ, Res.ok_bind, had, Res.ok_bind]
      exact (readL_sim hrel hrr hao w).1 hw
    · intro hw
      obtain ⟨μ, hμ, hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨ad, had, hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨⟨_, hg⟩, hrel⟩ := hme μ hμ
      obtain ⟨⟨_, hg'⟩, hao⟩ := hae ad had
      rw [hg, Res.ok_bind, hg', Res.ok_bind]
      exact (readL_sim hrel hrr hao w).2 hw
  | .app2 .mlen m i, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨⟨hm, hi⟩, hr⟩ := hf
    obtain ⟨M, g, hM, hmr, hme⟩ := hM m (by lsize_tac) hm
    obtain ⟨k, g', hI, hie⟩ := hI i (by lsize_tac) hi
    simp only [hM, hI, mlenOk] at hr
    obtain ⟨r, hrr⟩ := Option.isSome_iff_exists.1 hr
    simp only [Tm.toL, Op2.toLAt, Op2.toL, hM, hI, hrr]
    intro w
    rw [seqL_eval, seqL_eval]
    simp only [tm_eval]
    constructor
    · intro hw
      obtain ⟨_, hg, hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨_, hg', hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨μ, hμ⟩ := hmr ⟨_, hg⟩
      obtain ⟨-, hrel⟩ := hme μ hμ
      have hid := (hie _).2 ⟨rfl, _, hg'⟩
      rw [hμ, Res.ok_bind, hid, Res.ok_bind]
      exact (mlenL_sim hrel hrr w).1 hw
    · intro hw
      obtain ⟨μ, hμ, hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨id, hid, hw⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨⟨_, hg⟩, hrel⟩ := hme μ hμ
      obtain ⟨rfl, _, hg'⟩ := (hie id).1 hid
      rw [hg, Res.ok_bind, hg', Res.ok_bind]
      exact (mlenL_sim hrel hrr w).2 hw
  | .net _, _, hf | .netOf _ _, _, hf => by
    simp only [Tm.inL, Bool.false_eq_true, Op1.inL] at hf

/-- **A path, pushed in, is the path the program took**: the program's
path returns exactly where the path pushed in does and every index on it is
in bounds of the storage the updates left (`LiveTo`).  Example: `values[i]`
returns in neither where `i` is past the end. -/
theorem PTerm.toL_step (h : Rel σ ρ τ) {n : Nat}
    (hT : TermOK C σ τ ρ n) (hP : PathOK C σ τ ρ n) (_hI : IdOK C σ τ ρ n)
    (_hA : AddrOK C σ τ ρ n) (_hM : MemOK C σ τ ρ n) (_hV : MValOK C σ τ ρ n) :
    PathOK C σ τ ρ (n + 1) := fun p hn hf qs => match p, hn, hf, qs with
  | .root r, hn, _, qs => by
    simp only [Tm.toL, Op0.toL, LPath.eval, tm_eval]
    constructor
    · rintro ⟨rs, hrs, rfl⟩
      cases hrs
      exact ⟨rfl, LiveTo.of_noAt _ rfl⟩
    · rintro ⟨hq, -⟩
      cases hq
      exact ⟨(r, []), rfl, rfl⟩
  | .pv x, hn, hf, qs => by
    have hx := h.env x
    rw [Close.PTerm.eval_pv]
    simp only [Tm.inL] at hf
    rcases hl : lookupBy x ρ.env with _ | ⟨t⟩ | ⟨q⟩ | _ | ⟨S⟩ | ⟨k⟩ <;> rw [hl] at hx hf <;>
      simp only [EnvRel, Bool.false_eq_true] at hx hf <;>
      simp only [Tm.toL, hl]
    · obtain ⟨v, _, h₂⟩ := hx
      simp only [bind, Except.bind, h₂, Close.bindingPath, reduceCtorEq, false_and, exists_const,
          LPath.stuck, LPath.eval, LTerm.eval]
    · obtain ⟨r, segs, h₁, h₂, hlive⟩ := hx
      simp only [h₂, h₁, Res.ok_bind, Close.bindingPath]
      constructor
      · rintro ⟨rs, hrs, rfl⟩
        cases hrs
        exact ⟨rfl, hlive⟩
      · rintro ⟨hq, -⟩
        cases hq
        exact ⟨(r, segs), rfl, rfl⟩
  | .field p f, hn, hf, qs => by
    simp only [Tm.inL, Op1.inL] at hf
    rw [Close.PTerm.eval_field]
    simp only [Tm.toL, Op1.toL, LPath.eval]
    constructor
    · rintro ⟨rs', hrs', rfl⟩
      obtain ⟨rs, hrs, he⟩ := Res.bind_eq_ok.1 hrs'
      cases he
      obtain ⟨hq, hl⟩ := (hP p (by lsize_tac) hf _).1 ⟨rs, hrs, rfl⟩
      refine ⟨by rw [hq]; rfl, ?_⟩
      show LiveTo _ ((.field rs.1 :: rs.2) ++ [.field f])
      unfold LiveTo
      rw [lastAtSegs_field]
      exact hl
    · rintro ⟨hq, hl⟩
      obtain ⟨qs₀, hq₀, he⟩ := Res.bind_eq_ok.1 hq
      cases he
      have hl₀ : LiveTo (.struct τ.storage) qs₀ := by unfold LiveTo at hl ⊢; rw [lastAtSegs_field] at hl; exact hl
      obtain ⟨rs, hrs, rfl⟩ := (hP p (by lsize_tac) hf qs₀).2 ⟨hq₀, hl₀⟩
      exact ⟨(rs.1, rs.2 ++ [.field f]), by rw [hrs]; rfl, by simp only [List.cons_append]⟩
  | .at p i, hn, hf, qs => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    have hi := hT i (by lsize_tac) hf.2
    rw [Close.PTerm.eval_at]
    simp only [Tm.toL, Op2.toLAt, Op2.toL, LPath.eval]
    constructor
    · rintro ⟨rs', hrs', rfl⟩
      obtain ⟨rs, hrs, hr⟩ := Res.bind_eq_ok.1 hrs'
      obtain ⟨k, hk, hr⟩ := Res.bind_eq_ok.1 hr
      obtain ⟨v, hv, hk⟩ := Res.bind_eq_ok.1 hk
      obtain ⟨u, hu, he⟩ := Res.bind_eq_ok.1 hr
      cases he
      rw [Close.checkIndex_eq] at hu
      obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
      obtain ⟨hq, hl⟩ := (hP p (by lsize_tac) hf.1 _).1 ⟨rs, hrs, rfl⟩
      refine ⟨by rw [hq, Res.ok_bind, (hi v).2 hv, Res.ok_bind, hk]; rfl, ?_⟩
      show LiveTo _ ((.field rs.1 :: rs.2) ++ [.at k])
      unfold LiveTo
      rw [lastAtSegs_at, SVal.findLive_append, ← hl.find_eq, find_root, hc, Res.ok_bind]
      exact (idx_iff c k).1 (by cases u; exact hu)
    · rintro ⟨hq, hl⟩
      obtain ⟨qs₀, hq₀, hq⟩ := Res.bind_eq_ok.1 hq
      obtain ⟨k, hk, he⟩ := Res.bind_eq_ok.1 hq
      cases he
      obtain ⟨v, hv, hk⟩ := Res.bind_eq_ok.1 hk
      obtain ⟨c', hc'⟩ := hl
      rw [lastAtSegs_at, SVal.findLive_append] at hc'
      obtain ⟨c, hc, hck⟩ := Res.bind_eq_ok.1 hc'
      have hl₀ := LiveTo.of_findLive hc
      obtain ⟨rs, hrs, rfl⟩ := (hP p (by lsize_tac) hf.1 qs₀).2 ⟨hq₀, hl₀⟩
      refine ⟨(rs.1, rs.2 ++ [.at k]), ?_, by simp only [List.cons_append]⟩
      have hfs : τ.findStorage rs.1 rs.2 = .ok c := by rw [← find_root, hl₀.find_eq]; exact hc
      rw [hrs, Res.ok_bind, (hi v).1 hv, Res.ok_bind, hk, Res.ok_bind, Close.checkIndex_eq,
        hfs, Res.ok_bind, (idx_iff c k).2 ⟨c', hck⟩, Res.ok_bind]
  | .next _, hn, hf, _ => by simp only [Tm.inL, Op1.inL, Bool.false_eq_true] at hf
  | .nextIn _ _, hn, hf, _ => by simp only [Tm.inL, Op2.inL, Bool.false_eq_true] at hf
  | .atIn _ _ _, hn, hf, _ => by simp only [Tm.inL, Op3.inL, Bool.false_eq_true] at hf

/-- **An identity, pushed in**: the offset of the object the term names,
and a guard that returns exactly where the term does. -/
theorem ITerm.toL_step (h : Rel σ ρ τ) {n : Nat}
    (hT : TermOK C σ τ ρ n) (_hP : PathOK C σ τ ρ n) (_hI : IdOK C σ τ ρ n)
    (hA : AddrOK C σ τ ρ n) (hM : MemOK C σ τ ρ n) (_hV : MValOK C σ τ ρ n) :
    IdOK C σ τ ρ (n + 1) := fun i hn hf => match i, hn, hf with
  | .pvI x, hn, hf => by
    have hx := h.env x
    simp only [Tm.inL] at hf
    split at hf
    · rename_i k hl
      rw [hl] at hx
      simp only [EnvRel] at hx
      refine ⟨k, .lit (.bool true), by simp only [Tm.toL, hl], fun id => ?_⟩
      rw [Close.ITerm.eval_pv, hx]
      simp only [Res.ok_bind, Close.bindingRef_mref, Except.ok.injEq, LTerm.eval]
      exact ⟨fun h => ⟨h.symm, _, rfl⟩, fun h => h.1.symm⟩
    · cases hf
  | .app1 (.alloc R) m, hn, hf => by
    simp only [Tm.inL, Op1.inL, Bool.and_eq_true] at hf
    obtain ⟨hm, hs⟩ := hf
    obtain ⟨M, g, hM, hmr, hme⟩ := hM m (by lsize_tac) hm
    simp only [hM, Op1.toL, Option.bind_some, Option.isSome_map] at hs
    obtain ⟨⟨M', k⟩, hk⟩ := Option.isSome_iff_exists.1 hs
    refine ⟨k, g, by simp only [Tm.toL, Op1.toL, hM, Option.bind_some, hk, Option.map_some],
      fun id => ?_⟩
    rw [Close.ITerm.eval_alloc]
    constructor
    · intro hid
      obtain ⟨μ, hμ, hid⟩ := Res.bind_eq_ok.1 hid
      obtain ⟨hg, hrel⟩ := hme μ hμ
      obtain ⟨μ', ha, -⟩ := sallocR_rel (ev := fun t : LTerm => t.eval σ) (lit := LTerm.lit) (fun _ => rfl) hrel hk
      rw [ha] at hid
      cases hid
      exact ⟨rfl, hg⟩
    · rintro ⟨rfl, hg⟩
      obtain ⟨μ, hμ⟩ := hmr hg
      obtain ⟨-, hrel⟩ := hme μ hμ
      obtain ⟨μ', ha, -⟩ := sallocR_rel (ev := fun t : LTerm => t.eval σ) (lit := LTerm.lit) (fun _ => rfl) hrel hk
      rw [hμ, Res.ok_bind, ha]
      rfl
  | .app2 .iread m a, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨⟨hm, ha⟩, hs⟩ := hf
    obtain ⟨M, g, hM, hmr, hme⟩ := hM m (by lsize_tac) hm
    obtain ⟨k, sel, g', hA, har, hae⟩ := hA a (by lsize_tac) ha
    simp only [hM, hA, Op2.toL, Option.isSome_map] at hs
    obtain ⟨k', hk⟩ := Option.isSome_iff_exists.1 hs
    refine ⟨k', seqL g g', by simp only [Tm.toL, Op2.toLAt, Op2.toL, hM, hA, hk, Option.map_some],
      fun id => ?_⟩
    rw [Close.ITerm.eval_read, seqL_eval]
    constructor
    · intro hid
      obtain ⟨μ, hμ, hid⟩ := Res.bind_eq_ok.1 hid
      obtain ⟨ad, had, hid⟩ := Res.bind_eq_ok.1 hid
      obtain ⟨⟨_, hg⟩, hrel⟩ := hme μ hμ
      obtain ⟨⟨_, hg'⟩, hao⟩ := hae ad had
      rw [ireadL_eq hrel hk hao] at hid
      cases hid
      exact ⟨rfl, _, by rw [hg, Res.ok_bind, hg']⟩
    · rintro ⟨rfl, _, hgg⟩
      obtain ⟨_, hg, hg'⟩ := Res.bind_eq_ok.1 hgg
      obtain ⟨μ, hμ⟩ := hmr ⟨_, hg⟩
      obtain ⟨-, hrel⟩ := hme μ hμ
      obtain ⟨ad, had⟩ := har ⟨_, hg'⟩
      obtain ⟨-, hao⟩ := hae ad had
      rw [hμ, Res.ok_bind, had, Res.ok_bind, ireadL_eq hrel hk hao]
  | .app2 .copy m v, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨⟨hm, hv⟩, hs⟩ := hf
    obtain ⟨M, g, hMm, hmr, hme⟩ := hM m (by lsize_tac) hm
    match v, hv, hs with
    | .app1 .sval _, _, hs | .app2 .copyMem _ _, _, hs | .app2 .sfind _ _, _, hs =>
      simp only [Tm.toL, Op1.toL, Op2.toLAt, Op2.toL, hMm, Option.isSome_none,
        Bool.false_eq_true] at hs
    | .app1 (.newArr R) nt, hv, hs =>
      simp only [Tm.inL, Op1.inL] at hv
      have hnt := hT nt (by lsize_tac) hv
      simp only [Tm.toL, Op1.toL, Op2.toL, hMm] at hs
      split at hs
      · rename_i c hgr
        rw [Option.isSome_map] at hs
        obtain ⟨⟨M', k⟩, hk⟩ := Option.isSome_iff_exists.1 hs
        have hc : nt.eval τ = .ok (.int c) := (hnt _).1 (LTerm.ground?_eval σ _ hgr)
        have hv' : (Tm.app1 (Op1.newArr R) nt).eval τ = .ok (newArrVal R c) := by
          simp only [Tm.eval, Op1.eval, hc, bind, Except.bind, Value.asInt, pure, Except.pure]
        refine ⟨k, g, by simp only [Tm.toL, Op2.toLAt, Op2.toL, Op1.toL, hMm, hgr, hk,
          Option.map_some], fun id => ?_⟩
        rw [Close.ITerm.eval_copy, hv', Res.ok_bind]
        constructor
        · intro hid
          obtain ⟨μ, hμ, hid⟩ := Res.bind_eq_ok.1 hid
          obtain ⟨hg, hrel⟩ := hme μ hμ
          obtain ⟨μ', ha, -⟩ := sallocNew_rel (ev := fun t : LTerm => t.eval σ) (lit := LTerm.lit)
            (fun _ => rfl) hrel hk
          rw [ha] at hid
          cases hid
          exact ⟨rfl, hg⟩
        · rintro ⟨rfl, hg⟩
          obtain ⟨μ, hμ⟩ := hmr hg
          obtain ⟨-, hrel⟩ := hme μ hμ
          obtain ⟨μ', ha, -⟩ := sallocNew_rel (ev := fun t : LTerm => t.eval σ) (lit := LTerm.lit)
            (fun _ => rfl) hrel hk
          rw [hμ, Res.ok_bind, ha]
          rfl
      · simp only [Option.isSome_none, Bool.false_eq_true] at hs

/-- **An address, pushed in**: the object and what selects in it. -/
theorem MAddr.toL_step (_h : Rel σ ρ τ) {n : Nat}
    (hT : TermOK C σ τ ρ n) (_hP : PathOK C σ τ ρ n) (hI : IdOK C σ τ ρ n)
    (_hA : AddrOK C σ τ ρ n) (_hM : MemOK C σ τ ρ n) (_hV : MValOK C σ τ ρ n) :
    AddrOK C σ τ ρ (n + 1) := fun a hn hf => match a, hn, hf with
  | .app1 (.mfield f) i, hn, hf => by
    simp only [Tm.inL, Op1.inL] at hf
    obtain ⟨k, g, hI, hie⟩ := hI i (by lsize_tac) hf
    refine ⟨k, .fld f, g, by simp only [Tm.toL, Op1.toL, hI, Option.map_some], fun hg => ?_,
      fun ad had => ?_⟩
    · exact ⟨_, by rw [Close.MAddr.eval_field, (hie _).2 ⟨rfl, hg⟩, Res.ok_bind]⟩
    · rw [Close.MAddr.eval_field] at had
      obtain ⟨id, hid, had⟩ := Res.bind_eq_ok.1 had
      obtain ⟨rfl, hg⟩ := (hie id).1 hid
      cases had
      exact ⟨hg, rfl⟩
  | .app2 .mat i t, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨k, g, hI, hie⟩ := hI i (by lsize_tac) hf.1
    have ht := hT t (by lsize_tac) hf.2
    refine ⟨k, .idx (t.toL ρ), seqL g (isIntL (t.toL ρ)),
      by simp only [Tm.toL, Op2.toLAt, Op2.toL, hI, Option.map_some], fun ⟨w, hw⟩ => ?_,
      fun ad had => ?_⟩
    · rw [seqL_eval] at hw
      obtain ⟨_, hg, hi⟩ := Res.bind_eq_ok.1 hw
      obtain ⟨j, hj⟩ := (isIntL_ret σ _).1 ⟨_, hi⟩
      refine ⟨.memoryIndex (σ.nextId + k) j, ?_⟩
      rw [Close.MAddr.eval_at, (hie _).2 ⟨rfl, _, hg⟩, Res.ok_bind, (ht _).1 hj]
      rfl
    · rw [Close.MAddr.eval_at] at had
      obtain ⟨id, hid, had⟩ := Res.bind_eq_ok.1 had
      obtain ⟨rfl, _, hg⟩ := (hie id).1 hid
      obtain ⟨j, hj, had⟩ := Res.bind_eq_ok.1 had
      obtain ⟨w, hw, hj⟩ := Res.bind_eq_ok.1 hj
      cases w with
      | bool b => cases hj
      | int j' =>
        cases hj
        cases had
        have hw' := (ht _).2 hw
        obtain ⟨_, hi⟩ := (isIntL_ret σ _).2 ⟨_, hw'⟩
        exact ⟨⟨_, by rw [seqL_eval, hg, Res.ok_bind, hi]⟩, j, hw', rfl⟩

/-- **A memory, pushed in**: the objects after it, and a guard that
returns exactly where the term does. -/
theorem MTerm.toL_step (h : Rel σ ρ τ) {n : Nat}
    (hT : TermOK C σ τ ρ n) (_hP : PathOK C σ τ ρ n) (_hI : IdOK C σ τ ρ n)
    (hA : AddrOK C σ τ ρ n) (hM : MemOK C σ τ ρ n) (hV : MValOK C σ τ ρ n) :
    MemOK C σ τ ρ (n + 1) := fun m hn hf => match m, hn, hf with
  | .app0 .memory, hn, _ => by
    refine ⟨ρ.mem, .lit (.bool true), rfl, fun _ => ⟨τ, rfl⟩, fun μ hμ => ?_⟩
    cases hμ
    exact ⟨⟨_, rfl⟩, h.mem⟩
  | .app1 (.addM R) m, hn, hf => by
    simp only [Tm.inL, Op1.inL, Bool.and_eq_true] at hf
    obtain ⟨hm, hs⟩ := hf
    obtain ⟨M, g, hM, hmr, hme⟩ := hM m (by lsize_tac) hm
    simp only [hM, Op1.toL, Option.bind_some, Option.isSome_map] at hs
    obtain ⟨⟨M', k⟩, hk⟩ := Option.isSome_iff_exists.1 hs
    refine ⟨M', g, by simp only [Tm.toL, Op1.toL, hM, Option.bind_some, hk, Option.map_some],
      fun hg => ?_, fun μ' hμ' => ?_⟩
    · obtain ⟨μ, hμ⟩ := hmr hg
      obtain ⟨-, hrel⟩ := hme μ hμ
      obtain ⟨μ', ha, -⟩ := sallocR_rel (ev := fun t : LTerm => t.eval σ) (lit := LTerm.lit) (fun _ => rfl) hrel hk
      exact ⟨μ', by rw [Close.MTerm.eval_addM, hμ, Res.ok_bind, ha]; rfl⟩
    · rw [Close.MTerm.eval_addM] at hμ'
      obtain ⟨μ, hμ, hμ'⟩ := Res.bind_eq_ok.1 hμ'
      obtain ⟨hg, hrel⟩ := hme μ hμ
      obtain ⟨μ₁, ha, hrel'⟩ := sallocR_rel (ev := fun t : LTerm => t.eval σ) (lit := LTerm.lit) (fun _ => rfl) hrel hk
      rw [ha] at hμ'
      cases hμ'
      exact ⟨hg, hrel'⟩
  | .app2 .copySt m v, hn, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨⟨hm, hv⟩, hs⟩ := hf
    obtain ⟨M, g, hMm, hmr, hme⟩ := hM m (by lsize_tac) hm
    match v, hv, hs with
    | .app1 .sval _, _, hs | .app2 .copyMem _ _, _, hs | .app2 .sfind _ _, _, hs =>
      simp only [Tm.toL, Op1.toL, Op2.toLAt, Op2.toL, hMm, Option.isSome_none,
        Bool.false_eq_true] at hs
    | .app1 (.newArr R) nt, hv, hs =>
      simp only [Tm.inL, Op1.inL] at hv
      have hnt := hT nt (by lsize_tac) hv
      simp only [Tm.toL, Op1.toL, Op2.toL, hMm] at hs
      split at hs
      · rename_i c hgr
        rw [Option.isSome_map] at hs
        obtain ⟨⟨M', k⟩, hk⟩ := Option.isSome_iff_exists.1 hs
        have hc : nt.eval τ = .ok (.int c) := (hnt _).1 (LTerm.ground?_eval σ _ hgr)
        have hv' : (Tm.app1 (Op1.newArr R) nt).eval τ = .ok (newArrVal R c) := by
          simp only [Tm.eval, Op1.eval, hc, bind, Except.bind, Value.asInt, pure, Except.pure]
        refine ⟨M', g, by simp only [Tm.toL, Op2.toLAt, Op2.toL, Op1.toL, hMm, hgr, hk,
          Option.map_some], fun hg => ?_, fun μ' hμ' => ?_⟩
        · obtain ⟨μ, hμ⟩ := hmr hg
          obtain ⟨-, hrel⟩ := hme μ hμ
          obtain ⟨μ', ha, -⟩ := sallocNew_rel (ev := fun t : LTerm => t.eval σ) (lit := LTerm.lit)
            (fun _ => rfl) hrel hk
          exact ⟨μ', by rw [Close.MTerm.eval_copySt, hv', Res.ok_bind, hμ, Res.ok_bind, ha]; rfl⟩
        · rw [Close.MTerm.eval_copySt, hv', Res.ok_bind] at hμ'
          obtain ⟨μ, hμ, hμ'⟩ := Res.bind_eq_ok.1 hμ'
          obtain ⟨hg, hrel⟩ := hme μ hμ
          obtain ⟨μ₁, ha, hrel'⟩ := sallocNew_rel (ev := fun t : LTerm => t.eval σ)
            (lit := LTerm.lit) (fun _ => rfl) hrel hk
          rw [ha] at hμ'
          cases hμ'
          exact ⟨hg, hrel'⟩
      · simp only [Option.isSome_none, Bool.false_eq_true] at hs
  | .app3 .write m a v, hn, hf => by
    simp only [Tm.inL, Op3.inL, Bool.and_eq_true] at hf
    obtain ⟨⟨⟨hm, ha⟩, hv⟩, hs⟩ := hf
    obtain ⟨M, g, hM, hmr, hme⟩ := hM m (by lsize_tac) hm
    obtain ⟨k, sel, g', hA, har, hae⟩ := hA a (by lsize_tac) ha
    obtain ⟨sv, g'', hV, hvok, hve⟩ := hV v (by lsize_tac) hv
    simp only [hM, hA, hV, Op3.toL, Option.isSome_map] at hs
    obtain ⟨⟨M', gw⟩, hw⟩ := Option.isSome_iff_exists.1 hs
    refine ⟨M', seqL g'' (seqL g (seqL g' gw)),
      by simp only [Tm.toL, Op3.toL, hM, hA, hV, hw, Option.map_some], fun ⟨w, hgg⟩ => ?_,
      fun μ' hμ' => ?_⟩
    · rw [seqL_eval] at hgg
      obtain ⟨_, hg'', hgg⟩ := Res.bind_eq_ok.1 hgg
      rw [seqL_eval] at hgg
      obtain ⟨_, hg, hgg⟩ := Res.bind_eq_ok.1 hgg
      rw [seqL_eval] at hgg
      obtain ⟨_, hg', hgw⟩ := Res.bind_eq_ok.1 hgg
      obtain ⟨μ, hμ⟩ := hmr ⟨_, hg⟩
      obtain ⟨-, hrel⟩ := hme μ hμ
      obtain ⟨ad, had⟩ := har ⟨_, hg'⟩
      obtain ⟨-, hao⟩ := hae ad had
      have hsok := hvok ⟨_, hg''⟩
      have hv' : v.eval τ = .ok (sv.conc (fun t => t.eval σ) σ.nextId) :=
        (hve _).2 ⟨⟨_, hg''⟩, hsok, rfl⟩
      obtain ⟨μ', hw'⟩ := (writeL_rel hrel hw hsok hao).1.1 ⟨_, hgw⟩
      exact ⟨μ', by rw [Close.MTerm.eval_write, hv', Res.ok_bind, hμ, Res.ok_bind, had,
        Res.ok_bind, hw']⟩
    · rw [Close.MTerm.eval_write] at hμ'
      obtain ⟨mv, hmv, hμ'⟩ := Res.bind_eq_ok.1 hμ'
      obtain ⟨μ, hμ, hμ'⟩ := Res.bind_eq_ok.1 hμ'
      obtain ⟨ad, had, hμ'⟩ := Res.bind_eq_ok.1 hμ'
      obtain ⟨⟨_, hg''⟩, hsok, rfl⟩ := (hve mv).1 hmv
      obtain ⟨⟨_, hg⟩, hrel⟩ := hme μ hμ
      obtain ⟨⟨_, hg'⟩, hao⟩ := hae ad had
      obtain ⟨hiff, hrel'⟩ := writeL_rel hrel hw hsok hao
      obtain ⟨wg, hgw⟩ := hiff.2 ⟨_, hμ'⟩
      refine ⟨⟨wg, ?_⟩, hrel' _ hμ'⟩
      rw [seqL_eval, hg'', Res.ok_bind, seqL_eval, hg, Res.ok_bind, seqL_eval, hg', Res.ok_bind,
        hgw]

/-- **A memory value, pushed in**: the slot it writes. -/
theorem MValT.toL_step (_h : Rel σ ρ τ) {n : Nat}
    (hT : TermOK C σ τ ρ n) (_hP : PathOK C σ τ ρ n) (hI : IdOK C σ τ ρ n)
    (_hA : AddrOK C σ τ ρ n) (_hM : MemOK C σ τ ρ n) (_hV : MValOK C σ τ ρ n) :
    MValOK C σ τ ρ (n + 1) := fun v hn hf => match v, hn, hf with
  | .app1 .mval t, hn, hf => by
    simp only [Tm.inL, Op1.inL] at hf
    have ht := hT t (by lsize_tac) hf
    refine ⟨.val (t.toL ρ), t.toL ρ, by simp only [Tm.toL, Op1.toL], fun hg => hg,
      fun mv => ?_⟩
    rw [Close.MValT.eval_val]
    constructor
    · intro hmv
      obtain ⟨w, hw, hmv⟩ := Res.bind_eq_ok.1 hmv
      cases hmv
      have hw' := (ht w).2 hw
      exact ⟨⟨w, hw'⟩, ⟨w, hw'⟩, (SMV.conc_val hw').symm⟩
    · rintro ⟨-, ⟨w, hw⟩, rfl⟩
      rw [(ht w).1 hw, Res.ok_bind, SMV.conc_val hw]
  | .app1 .ref i, hn, hf => by
    simp only [Tm.inL, Op1.inL] at hf
    obtain ⟨k, g, hI, hie⟩ := hI i (by lsize_tac) hf
    refine ⟨.ref k, g, by simp only [Tm.toL, Op1.toL, hI, Option.map_some], fun _ => trivial,
      fun mv => ?_⟩
    rw [Close.MValT.eval_ref]
    constructor
    · intro hmv
      obtain ⟨id, hid, hmv⟩ := Res.bind_eq_ok.1 hmv
      obtain ⟨rfl, hg⟩ := (hie id).1 hid
      cases hmv
      exact ⟨hg, trivial, rfl⟩
    · rintro ⟨hg, -, rfl⟩
      rw [(hie _).2 ⟨rfl, hg⟩]
      rfl

/-- All six at every size. -/
theorem Rel.all_ok (h : Rel σ ρ τ) : (n : Nat) →
    TermOK C σ τ ρ n ∧ PathOK C σ τ ρ n ∧ IdOK C σ τ ρ n ∧ AddrOK C σ τ ρ n ∧
      MemOK C σ τ ρ n ∧ MValOK C σ τ ρ n
  | 0 => ⟨fun _ hn => absurd hn (Nat.not_lt_zero _), fun _ hn => absurd hn (Nat.not_lt_zero _),
      fun _ hn => absurd hn (Nat.not_lt_zero _), fun _ hn => absurd hn (Nat.not_lt_zero _),
      fun _ hn => absurd hn (Nat.not_lt_zero _), fun _ hn => absurd hn (Nat.not_lt_zero _)⟩
  | n + 1 =>
    have ⟨hT, hP, hI, hA, hM, hV⟩ := Rel.all_ok h n
    ⟨Term.toL_step h hT hP hI hA hM hV, PTerm.toL_step h hT hP hI hA hM hV,
      ITerm.toL_step h hT hP hI hA hM hV, MAddr.toL_step h hT hP hI hA hM hV,
      MTerm.toL_step h hT hP hI hA hM hV, MValT.toL_step h hT hP hI hA hM hV⟩

theorem Term.toL_eval (h : Rel σ ρ τ) (t : Term C) (hf : t.inL ρ = true) :
    Sim ((t.toL ρ).eval σ) (t.eval τ) :=
  (h.all_ok _).1 t (Nat.lt_succ_self _) hf

theorem PTerm.toL_chk (h : Rel σ ρ τ) (p : PTerm C) (hf : p.inL ρ = true) (qs : List Seg) :
    (∃ rs, p.eval τ = .ok rs ∧ qs = .field rs.1 :: rs.2) ↔
      ((p.toL ρ).eval σ = .ok qs ∧ LiveTo (.struct τ.storage) qs) :=
  (h.all_ok _).2.1 p (Nat.lt_succ_self _) hf qs

theorem ITerm.toL_eval (h : Rel σ ρ τ) (i : ITerm C) (hf : i.inL ρ = true) :
    ∃ k g, i.toL ρ = some (k, g) ∧
      ∀ id, i.eval τ = .ok id ↔ (id = σ.nextId + k ∧ ∃ v, g.eval σ = .ok v) :=
  (h.all_ok _).2.2.1 i (Nat.lt_succ_self _) hf

theorem MTerm.toL_eval (h : Rel σ ρ τ) (m : MTerm C) (hf : m.inL ρ = true) :
    ∃ M g, m.toL ρ = some (M, g) ∧
      ((∃ v, g.eval σ = .ok v) → ∃ μ, m.eval τ = .ok μ) ∧
      ∀ μ, m.eval τ = .ok μ → (∃ v, g.eval σ = .ok v) ∧
        MemRel (fun t => t.eval σ) σ.nextId M μ :=
  (h.all_ok _).2.2.2.2.1 m (Nat.lt_succ_self _) hf

/-- A storage term, pushed in, is the write it made.  Example:
`delAt(storage, alice.account)`. -/
theorem STerm.toL_eval (h : Rel σ ρ τ) :
    (s : STerm C) → s.inL ρ = true →
      Sim ((s.toL ρ).eval σ) (s.eval τ >>= fun τ' => .ok (.struct τ'.storage))
  | .app0 .storage, _ => Sim.of_eq (by rw [Tm.toL, Op0.toL, h.stor]; rfl)
  | .app3 .save s p v, hf => by
    simp only [Tm.inL, Op3.inL, Bool.and_eq_true] at hf
    obtain ⟨⟨⟨hs, hp⟩, hv⟩, hz⟩ := hf
    obtain rfl := STerm.isStorage_eq hs
    match v, hv with
    | .app1 .sval t, hv =>
      have hf : p.inL ρ = true ∧ t.inL ρ = true := ⟨hp, hv⟩
      have ht := Term.toL_eval h t hf.2
      have hb := live_bridge (PTerm.toL_chk h p hf.1)
      rw [Close.STerm.eval_save]
      simp only [Tm.toL, Op0.toL, Op1.toL, Op3.toL, LStor.eval, h.stor, Res.ok_bind,
          Close.STerm.eval_storage]
      intro a
      simp only [Res.bind_eq_ok]
      constructor
      · rintro ⟨x, hx, qs, hq, ha⟩
        obtain ⟨c, hc⟩ := findLive_of_saveLive ha
        obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
        rw [saveLive_eq_save _ hc, save_root] at ha
        obtain ⟨τ'', h'', he⟩ := Res.bind_eq_ok.1 ha
        exact ⟨τ'', ⟨x, (ht x).1 hx, rs, hrs, h''⟩, he⟩
      · rintro ⟨τ'', ⟨x, hx, rs, hrs, h''⟩, he⟩
        have hsv : (SVal.struct τ.storage).save (.field rs.1 :: rs.2) x.toSVal = .ok a := by
          rw [save_root, h'', Res.ok_bind, he]
        obtain ⟨c, hc⟩ := find_of_save hsv
        rw [find_root] at hc
        obtain ⟨hq, hl⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hc⟩
        exact ⟨x, (ht x).2 hx, _, hq, by rw [saveLive_eq_save _ hl]; exact hsv⟩
    | .app2 .sfind s' p', hv =>
      simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hv
      obtain ⟨hs', hp'⟩ := hv
      obtain rfl := STerm.isStorage_eq hs'
      have hb := live_bridge (PTerm.toL_chk h p hp)
      have hb' := live_bridge (PTerm.toL_chk h p' hp')
      rw [Close.STerm.eval_save_find, Close.SValT.eval_find]
      simp only [Tm.toL, Op0.toL, Op2.toLAt, Op2.toL, Op3.toL, LStor.eval, h.stor, Res.ok_bind,
        Close.STerm.eval_storage, bind_assoc]
      exact read_bridge hb' fun n => write_bridge hb fun c => .ok (c.overlay n)
    | .app1 (.newArr _) _, _ =>
      simp only [Tm.toL, Op1.toL, LVal.storable, Bool.false_eq_true] at hz
    | .app2 .copyMem _ _, hv =>
      simp only [Tm.inL, Bool.false_eq_true, Op2.inL] at hv
  | .app2 .delAt s p, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨hs, hf⟩ := hf
    obtain rfl := STerm.isStorage_eq hs
    have hb := live_bridge (PTerm.toL_chk h p hf)
    rw [Close.STerm.eval_delAt]
    simp only [Tm.toL, Op0.toL, Op2.toLAt, Op2.toL, LStor.eval, h.stor, Res.ok_bind,
        Close.STerm.eval_storage]
    intro a
    simp only [Res.bind_eq_ok]
    constructor
    · rintro ⟨qs, hq, c, hc, ha⟩
      obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
      rw [saveLive_eq_save _ hc, save_root] at ha
      obtain ⟨τ'', h'', he⟩ := Res.bind_eq_ok.1 ha
      exact ⟨τ'', ⟨rs, hrs, c, hfs, h''⟩, he⟩
    · rintro ⟨τ'', ⟨rs, hrs, c, hfs, h''⟩, he⟩
      obtain ⟨hq, hl⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hfs⟩
      refine ⟨_, hq, c, hl, ?_⟩
      rw [saveLive_eq_save _ hl, save_root, h'', Res.ok_bind, he]
  | .pvS _, hf => by simp only [Tm.inL, Bool.false_eq_true] at hf
  | .app3 .push s p v, hf => by
    match v, hf with
    | .app1 .sval t, hf =>
      simp only [Tm.inL, Op3.inL, Op1.inL, Bool.and_eq_true] at hf
      obtain ⟨⟨hs, hp⟩, ht⟩ := hf
      obtain rfl := STerm.isStorage_eq hs
      have hb := live_bridge (PTerm.toL_chk h p hp)
      have htt := Term.toL_eval h t ht
      rw [Close.STerm.eval_push, Close.SValT.eval_val]
      simp only [Tm.toL, Op0.toL, Op1.toL, Op3.toL, LStor.eval, h.stor, Res.ok_bind,
        Close.STerm.eval_storage, bind_assoc]
      cases hx : t.eval τ with
      | ok x =>
        rw [(htt x).2 hx, Res.ok_bind]
        have hval : (fun _ : SVal => (Except.ok x : Res Value) >>= fun x =>
            (Except.ok x.toSVal : Res SVal) >>= fun sv => pure sv.strip) =
            fun _ => .ok x.toSVal := by
          funext _; cases x <;> rfl
        simp only [Res.ok_bind] at hval ⊢
        rw [hval]
        simp only [pushOn_word, bind_assoc]
        exact write_bridge hb _
      | error e =>
        refine Sim.halt (fun a ha => ?_) (fun a ha => ?_)
        · obtain ⟨y, hy, -⟩ := Res.bind_eq_ok.1 ha
          have := (htt y).1 hy
          rw [hx] at this; cases this
        · obtain ⟨rs, -, ha⟩ := Res.bind_eq_ok.1 ha
          obtain ⟨c, -, ha⟩ := Res.bind_eq_ok.1 ha
          obtain ⟨τ', hτ', -⟩ := Res.bind_eq_ok.1 ha
          cases c with
          | array es sh fx =>
            simp only [Close.pushOn_array, Res.error_bind] at hτ'
            cases hτ'
          | prim _ | struct _ | map _ _ => cases hτ'
    | .app2 .sfind s' p', hf =>
      simp only [Tm.inL, Op3.inL, Op2.inL, Bool.and_eq_true] at hf
      obtain ⟨⟨hs, hp⟩, hs', hp'⟩ := hf
      obtain rfl := STerm.isStorage_eq hs
      obtain rfl := STerm.isStorage_eq hs'
      rw [Close.STerm.eval_push, Close.SValT.eval_find]
      simp only [Tm.toL, Op0.toL, Op2.toLAt, Op2.toL, Op3.toL, Close.STerm.eval_storage,
          Res.ok_bind,
        bind_assoc]
      exact pushCopy_bridge h.stor (live_bridge (PTerm.toL_chk h p hp))
        (live_bridge (PTerm.toL_chk h p' hp'))
    | .app1 (.newArr _) _, hf | .app2 .copyMem _ _, hf =>
      simp only [Tm.inL, Op3.inL, Bool.false_eq_true] at hf
  | .app1 (.select _) _, hf => by simp only [Tm.inL, Op1.inL, Bool.false_eq_true] at hf
  | .app2 (.pushSlot E) s p, hf | .app2 (.extend E) s p, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨hs, hp⟩ := hf
    obtain rfl := STerm.isStorage_eq hs
    have hb := live_bridge (PTerm.toL_chk h p hp)
    first
      | rw [Close.STerm.eval_pushSlot]
      | rw [STerm.eval_extend]
    simp only [Tm.toL, Op0.toL, Op2.toLAt, Op2.toL, LStor.eval, LTerm.eval, h.stor, Res.ok_bind,
      Close.STerm.eval_storage, pushOn_slot _ E _ _ (.bool true), bind_assoc]
    exact write_bridge hb _
  | .app2 .pop s p, hf | .app2 .shrink s p, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨hs, hp⟩ := hf
    obtain rfl := STerm.isStorage_eq hs
    have hb := live_bridge (PTerm.toL_chk h p hp)
    first
      | rw [Close.STerm.eval_pop]
      | rw [Close.STerm.eval_shrink]
    simp only [Tm.toL, Op0.toL, Op2.toLAt, Op2.toL, LStor.eval, LTerm.eval, h.stor, Res.ok_bind,
      Close.STerm.eval_storage, popOn_pop _ _ _ _ (.bool true), bind_assoc]
    exact write_bridge hb _
end

/-- `Tm.sameL` is equality. -/
theorem Tm.sameL_eq {a b : Tm C s} (h : a.sameL b = true) : a = b := by
  simp only [Tm.sameL, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem Term.sameL_eq (a b : Term C) (h : a.sameL b = true) : a = b := Tm.sameL_eq h
theorem PTerm.sameL_eq (p q : PTerm C) (h : p.sameL q = true) : p = q := Tm.sameL_eq h

/-- What `Fml.eqDView` recognises is `eqD a b`. -/
theorem Fml.eqDView_some {φ ψ : Fml C} {a b : Term C} (h : Fml.eqDView φ ψ = some (a, b)) :
    φ = .defined a ∧ ψ = .and (.defined b) (.eq a b) := by
  unfold Fml.eqDView at h
  split at h
  · rename_i a₀ b₀ a' b'
    split at h
    · rename_i hs
      simp only [Bool.and_eq_true] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [← Term.sameL_eq _ _ hs.1, ← Term.sameL_eq _ _ hs.2]
      exact ⟨rfl, rfl⟩
    · cases h
  · cases h

theorem Term.eqLit_cases {a b : Term C} (h : a.eqLit b = true) :
    (a.isLitLike = true ∧ b.isAtom = true) ∨ (b.isLitLike = true ∧ a.isAtom = true) := by
  simpa only [Term.eqLit, Bool.or_eq_true, Bool.and_eq_true] using h

/-- A literal or `msg.sender` denotes the value it returns, pushed in or not. -/
theorem Term.litLike_val {σ τ : State} {ρ : Sym} (h : Rel σ ρ τ) {a : Term C}
    (ha : a.isLitLike = true) : ∃ w, a.denote τ = .prim w ∧ (a.toL ρ).eval σ = .ok w := by
  unfold Term.isLitLike at ha
  split at ha
  · exact ⟨_, rfl, rfl⟩
  · rename_i k
    exact ⟨.int (τ.envVal k), rfl, by simp only [Tm.toL, Op0.toL, LTerm.eval, h.tx k]⟩
  · cases ha

theorem Term.inL_of_isAtom {t : Term C} {ρ : Sym} (h : t.isAtom = true) : t.inL ρ = true := by
  unfold Term.isAtom at h
  split at h
  · rfl
  · rfl
  · cases h

/-- A literal or a local is `≐` a primitive exactly when it returns it: a
local bound to no value denotes the empty struct, no primitive. -/
theorem Term.atom_equiv_prim {τ : State} {t : Term C} (h : t.isAtom = true) (v : Value) :
    Theory.StValue.Equiv (t.denote τ) (.prim v) ↔ t.eval τ = .ok v := by
  rw [Theory.StValue.Equiv.prim_iff]
  unfold Term.isAtom at h
  split at h
  · simp only [Close.Term.denote_lit, Close.Term.eval_lit, Theory.StValue.prim.injEq,
      Except.ok.injEq]
  · rename_i x
    rw [Close.Term.denote_pv, Close.Term.eval_pv]
    cases τ.getEnv x with
    | ok b => cases b <;> simp only [Theory.StValue.prim.injEq, reduceCtorEq, bind, Except.bind,
        Close.bindingVal, Except.ok.injEq]
    | error e => simp only [reduceCtorEq, bind, Except.bind]
  · cases h

/-- An equation of the target language holds when both sides return, with
one value. -/
theorem LFml.holds_eq_iff (σ : State) (a b : LTerm) :
    (LFml.eq a b).holds σ ↔ ∃ x, a.eval σ = .ok x ∧ b.eval σ = .ok x := by
  simp only [LFml.holds]
  cases a.eval σ with
  | ok x =>
    cases b.eval σ with
    | ok y => exact ⟨fun h => ⟨x, rfl, h ▸ rfl⟩, fun ⟨_, h₁, h₂⟩ => by cases h₁; cases h₂; rfl⟩
    | error _ => exact ⟨False.elim, fun ⟨_, _, h⟩ => nomatch h⟩
  | error _ => exact ⟨False.elim, fun ⟨_, h, _⟩ => nomatch h⟩

/-- An update's term returns, as a formula: `eq g g`. -/
theorem holds_eq_self (σ : State) (g : LTerm) :
    (LFml.eq g g).holds σ ↔ ∃ v, g.eval σ = .ok v := by
  simp only [LFml.holds]
  cases g.eval σ <;> simp only [reduceCtorEq, exists_false, Except.ok.injEq, exists_eq']

/-- The guard of an update under the box: `[ x = e; ] φ` holds when `e`
halts. -/
theorem guardM_box (σ : State) (g : LTerm) (φ : LFml) :
    (guardM .box g φ).holds σ ↔ ((∃ v, g.eval σ = .ok v) → φ.holds σ) := by
  simp only [guardM, LFml.holds, ← holds_eq_self]

/-- Under the diamond: `⟨ x = e; ⟩ φ` does not hold when `e` halts. -/
theorem guardM_diamond (σ : State) (g : LTerm) (φ : LFml) :
    (guardM .diamond g φ).holds σ ↔ ((∃ v, g.eval σ = .ok v) ∧ φ.holds σ) := by
  simp only [guardM, LFml.holds, ← holds_eq_self]

/-- An update and its guard agree: the update runs exactly when its term
returns, and what follows agrees in the state it leaves. -/
theorem after_guardM {σ : State} {m : Modality} {x : Res State} {P : State → Prop} {g : LTerm}
    {ψ : LFml} (hg : (∃ v, g.eval σ = .ok v) ↔ ∃ τ', x = .ok τ')
    (hψ : ∀ τ', x = .ok τ' → (P τ' ↔ ψ.holds σ)) :
    m.after P x ↔ (guardM m g ψ).holds σ := by
  cases x with
  | error e =>
    have : ¬ ∃ v, g.eval σ = .ok v := by simp only [hg, reduceCtorEq, exists_false,
        not_false_eq_true]
    cases m <;> simp only [Modality.after, Modality.onHalt, guardM_diamond, this, false_and,
        guardM_box, false_implies]
  | ok τ' =>
    have : ∃ v, g.eval σ = .ok v := by simp only [hg, Except.ok.injEq, exists_eq']
    cases m <;> simp only [Modality.after, hψ τ' rfl, guardM_diamond, this, true_and, guardM_box,
        forall_const]

/-- **Pushing the updates in keeps the meaning**, halts included.

Example: `{ storage := save(storage, balances[k], 5) } find(storage, balances[k]) = 5`
holds exactly when `sok(save(init, balances[k], 5)) = sok(…) → find(save(init,
balances[k], 5), balances[k]) = 5` does, both read in the state before the
write. -/
theorem Fml.toL_holds :
    (φ : Fml C) → ∀ {σ τ : State} {ρ : Sym}, Rel σ ρ τ → φ.inL ρ = true →
      (holds τ φ ↔ (φ.toL ρ).holds σ)
  | .tt, _, _, _, _, _ => Iff.rfl
  | .eq a b, _, τ, _, h, hf => by
    simp only [Fml.inL] at hf
    simp only [holds, Fml.toL]
    rw [LFml.holds_eq_iff]
    rcases Term.eqLit_cases hf with ⟨hla, hb⟩ | ⟨hlb, ha⟩
    · obtain ⟨w, hd, hl⟩ := Term.litLike_val h hla
      have hs : Sim ((b.toL _).eval _) (b.eval τ) := Term.toL_eval h b (Term.inL_of_isAtom hb)
      rw [hd, Close.equiv_prim_left_iff, eq_comm, ← Theory.StValue.Equiv.prim_iff,
        Term.atom_equiv_prim hb]
      simp only [hl, Except.ok.injEq, exists_eq_left']
      exact (hs w).symm
    · obtain ⟨w, hd, hl⟩ := Term.litLike_val h hlb
      have hs : Sim ((a.toL _).eval _) (a.eval τ) := Term.toL_eval h a (Term.inL_of_isAtom ha)
      rw [hd, Term.atom_equiv_prim ha]
      simp only [hl, Except.ok.injEq, exists_eq_right']
      exact (hs w).symm
  | .defined t, _, _, _, h, hf => by
    have ht := Term.toL_eval h t hf
    simp only [holds, Fml.toL, LFml.holds]
    cases hx : (t.toL _).eval _ with
    | ok x => exact ⟨fun _ => rfl, fun _ => ⟨x, (ht x).1 hx⟩⟩
    | error _ =>
      refine ⟨fun ⟨v, hv⟩ => ?_, False.elim⟩
      have := (ht v).2 hv
      simp_all only [reduceCtorEq]
  | .not φ, _, _, _, h, hf => by
    simp only [Fml.inL] at hf
    simp only [holds, Fml.toL, LFml.holds, Fml.toL_holds φ h hf]
  | .and φ ψ, _, _, _, h, hf => by
    cases hv : Fml.eqDView φ ψ with
    | none =>
      simp only [Fml.inL, hv, Bool.and_eq_true] at hf
      simp only [holds, Fml.toL, hv, LFml.holds, Fml.toL_holds φ h hf.1, Fml.toL_holds ψ h hf.2]
    | some ab =>
      obtain ⟨a, b⟩ := ab
      simp only [Fml.inL, hv, Bool.and_eq_true] at hf
      simp only [Fml.toL, hv]
      obtain ⟨rfl, rfl⟩ := Fml.eqDView_some hv
      have ha : Sim ((a.toL _).eval _) (a.eval _) := Term.toL_eval h a hf.1
      have hb : Sim ((b.toL _).eval _) (b.eval _) := Term.toL_eval h b hf.2
      refine holds_eqD_iff.trans ?_
      rw [LFml.holds_eq_iff]
      exact exists_congr fun x => and_congr (ha x).symm (hb x).symm
  | .imp φ ψ, _, _, _, h, hf => by
    simp only [Fml.inL, Bool.and_eq_true] at hf
    simp only [holds, Fml.toL, LFml.holds, Fml.toL_holds φ h hf.1, Fml.toL_holds ψ h hf.2]
  | .upd m [] φ, _, τ, _, h, hf => by
    simp only [Fml.inL] at hf
    simp only [holds, Fml.toL, Upd.apply, List.foldlM_nil]
    exact Fml.toL_holds φ h hf
  | .upd m [e] φ, σ, τ, ρ, h, hf => by
    simp only [Fml.inL, Bool.and_eq_true] at hf
    simp only [holds, Fml.toL, Upd.apply, List.foldlM_cons, List.foldlM_nil, bind_pure]
    cases e with
    | val x t =>
      have ht := Term.toL_eval h t hf.1
      rw [Close.UpdElem.write_val]
      refine after_guardM (by
        simp only [UpdElem.toL, Res.bind_eq_ok]
        exact ⟨fun ⟨v, hv⟩ => ⟨_, v, (ht v).1 hv, rfl⟩, fun ⟨_, v, hv, _⟩ => ⟨v, (ht v).2 hv⟩⟩)
        fun τ' hτ => ?_
      obtain ⟨v, hv, he⟩ := Res.bind_eq_ok.1 hτ
      cases he
      refine Fml.toL_holds φ (h.bind x _ _ ?_) hf.2
      exact ⟨v, (ht v).2 hv, by simp only [State.getEnv_setEnv_self]⟩
    | path x p =>
      have hA := PTerm.toL_chk h p hf.1
      rw [Close.UpdElem.write_path]
      refine after_guardM (by
        simp only [UpdElem.toL]
        rw [guardPath_ok h.stor]
        simp only [Res.bind_eq_ok]
        constructor
        · rintro ⟨qs, hq, hl⟩
          obtain ⟨rs, hrs, -⟩ := (hA qs).2 ⟨hq, hl⟩
          exact ⟨_, rs, hrs, rfl⟩
        · rintro ⟨_, rs, hrs, -⟩
          obtain ⟨hq, hl⟩ := (hA _).1 ⟨rs, hrs, rfl⟩
          exact ⟨_, hq, hl⟩) fun τ' hτ => ?_
      obtain ⟨rs, hr, he⟩ := Res.bind_eq_ok.1 hτ
      cases he
      refine Fml.toL_holds φ (h.bind x _ _ ?_) hf.2
      obtain ⟨hq, hl⟩ := (hA _).1 ⟨rs, hr, rfl⟩
      exact ⟨rs.1, rs.2, hq, by simp only [State.getEnv_setEnv_self], hl⟩
    | storage s =>
      have hs := STerm.toL_eval h s hf.1
      rw [Close.UpdElem.write_storage]
      refine after_guardM (by
        simp only [UpdElem.toL, LTerm.eval, Res.bind_eq_ok]
        constructor
        · rintro ⟨_, v, hv, -⟩
          obtain ⟨τ₁, h₁, -⟩ := Res.bind_eq_ok.1 ((hs v).1 hv)
          exact ⟨_, τ₁, h₁, rfl⟩
        · rintro ⟨_, τ₁, h₁, -⟩
          exact ⟨_, _, (hs _).2 (by rw [h₁]; rfl), rfl⟩) fun τ' hτ => ?_
      obtain ⟨τ₁, h₁, he⟩ := Res.bind_eq_ok.1 hτ
      cases he
      refine Fml.toL_holds φ ⟨(hs _).2 (by rw [h₁]; rfl), fun y => ?_,
        fun k => by rw [← h.tx k]; cases k <;> rfl, h.mem.of_heap rfl rfl⟩ hf.2
      simp only [UpdElem.toL, lookupBy_onWrite]
      exact (h.env y).onWrite rfl
    | store x s =>
      have hs := STerm.toL_eval h s hf.1
      rw [Close.UpdElem.write_store]
      refine after_guardM (by
        simp only [UpdElem.toL, LTerm.eval, Res.bind_eq_ok]
        constructor
        · rintro ⟨_, v, hv, -⟩
          obtain ⟨τ₁, h₁, -⟩ := Res.bind_eq_ok.1 ((hs v).1 hv)
          exact ⟨_, τ₁, h₁, rfl⟩
        · rintro ⟨_, τ₁, h₁, -⟩
          exact ⟨_, _, (hs _).2 (by rw [h₁]; rfl), rfl⟩) fun τ' hτ => ?_
      obtain ⟨τ₁, h₁, he⟩ := Res.bind_eq_ok.1 hτ
      cases he
      refine Fml.toL_holds φ (h.bind x _ _ ?_) hf.2
      exact ⟨τ₁.storage, (hs _).2 (by rw [h₁]; rfl), by simp only [State.getEnv_setEnv_self]⟩
    | net r op a =>
      have hra : r.inL ρ = true ∧ a.inL ρ = true := by simpa only [UpdElem.inL,
          Bool.and_eq_true] using hf.1
      have hr := Term.toL_eval h r hra.1
      have ha := Term.toL_eval h a hra.2
      rw [Close.UpdElem.write_net]
      refine after_guardM ?_ fun τ' hτ => ?_
      · simp only [UpdElem.toL, LTerm.eval]
        constructor
        · rintro ⟨_, hv⟩
          obtain ⟨i, hi, hv⟩ := Res.bind_eq_ok.1 hv
          obtain ⟨x, hx, hi⟩ := Res.bind_eq_ok.1 hi
          obtain ⟨j, hj, -⟩ := Res.bind_eq_ok.1 hv
          obtain ⟨y, hy, hj⟩ := Res.bind_eq_ok.1 hj
          exact ⟨_, by simp only [(hr x).1 hx, (ha y).1 hy, Res.ok_bind, hi, hj]; rfl⟩
        · rintro ⟨τ', hτ⟩
          obtain ⟨i, hi, hτ⟩ := Res.bind_eq_ok.1 hτ
          obtain ⟨x, hx, hi⟩ := Res.bind_eq_ok.1 hi
          obtain ⟨j, hj, -⟩ := Res.bind_eq_ok.1 hτ
          obtain ⟨y, hy, hj⟩ := Res.bind_eq_ok.1 hj
          refine ⟨.bool true, ?_⟩
          simp only [(hr x).2 hx, (ha y).2 hy, Res.ok_bind, hi, hj]
          split <;> rfl
      · obtain ⟨i, -, hτ⟩ := Res.bind_eq_ok.1 hτ
        obtain ⟨j, -, hτ⟩ := Res.bind_eq_ok.1 hτ
        cases hτ
        exact Fml.toL_holds φ ⟨h.stor, fun y => h.env y, fun k => h.tx k,
          h.mem.of_heap rfl rfl⟩ hf.2
    | pay r a =>
      have hra : r.inL ρ = true ∧ a.inL ρ = true := by simpa only [UpdElem.inL,
          Bool.and_eq_true] using hf.1
      have hr := Term.toL_eval h r hra.1
      have ha := Term.toL_eval h a hra.2
      rw [Close.UpdElem.write_pay]
      refine after_guardM ?_ fun τ' hτ => ?_
      · simp only [UpdElem.toL, LTerm.eval]
        constructor
        · rintro ⟨_, hv⟩
          obtain ⟨i, hi, hv⟩ := Res.bind_eq_ok.1 hv
          obtain ⟨x, hx, hi⟩ := Res.bind_eq_ok.1 hi
          obtain ⟨j, hj, hv⟩ := Res.bind_eq_ok.1 hv
          obtain ⟨y, hy, hj⟩ := Res.bind_eq_ok.1 hj
          have hn : ¬ j < 0 := by
            intro hn
            rw [payGuard_eval σ _ hy hj, if_pos hn] at hv
            split at hv <;> cases hv
          exact ⟨_, by simp only [(hr x).1 hx, (ha y).1 hy, Res.ok_bind, hi, hj, if_neg hn]; rfl⟩
        · rintro ⟨τ', hτ⟩
          obtain ⟨i, hi, hτ⟩ := Res.bind_eq_ok.1 hτ
          obtain ⟨x, hx, hi⟩ := Res.bind_eq_ok.1 hi
          obtain ⟨j, hj, hτ⟩ := Res.bind_eq_ok.1 hτ
          obtain ⟨y, hy, hj⟩ := Res.bind_eq_ok.1 hj
          have hn : ¬ j < 0 := by intro hn; rw [if_pos hn] at hτ; cases hτ
          refine ⟨.bool true, ?_⟩
          simp only [(hr x).2 hx, (ha y).2 hy, Res.ok_bind, hi, hj]
          split <;> rw [payGuard_eval σ _ ((ha y).2 hy) hj, if_neg hn]
      · obtain ⟨i, -, hτ⟩ := Res.bind_eq_ok.1 hτ
        obtain ⟨j, -, hτ⟩ := Res.bind_eq_ok.1 hτ
        split at hτ
        · cases hτ
        · cases hτ
          exact Fml.toL_holds φ ⟨h.stor, fun y => h.env y, fun k => h.tx k,
          h.mem.of_heap rfl rfl⟩ hf.2
    | mref x i =>
      obtain ⟨k, g, hI, hie⟩ := ITerm.toL_eval h i hf.1
      have hf2 := hf.2
      simp only [UpdElem.toL, hI] at hf2 ⊢
      rw [Close.UpdElem.write_mref]
      refine after_guardM ?_ fun τ' hτ => ?_
      · simp only [Res.bind_eq_ok]
        constructor
        · rintro ⟨_, hg⟩
          exact ⟨_, _, (hie _).2 ⟨rfl, _, hg⟩, rfl⟩
        · rintro ⟨_, id, hid, -⟩
          exact ((hie id).1 hid).2
      · obtain ⟨id, hid, he⟩ := Res.bind_eq_ok.1 hτ
        cases he
        obtain ⟨rfl, -⟩ := (hie _).1 hid
        refine Fml.toL_holds φ (h.bind x _ _ ?_) hf2
        simp only [EnvRel, State.getEnv_setEnv_self]
    | memory mm =>
      obtain ⟨M, g, hM, hmr, hme⟩ := MTerm.toL_eval h mm hf.1
      have hf2 := hf.2
      simp only [UpdElem.toL, hM] at hf2 ⊢
      rw [Close.UpdElem.write_memory]
      refine after_guardM ?_ fun τ' hτ => ?_
      · constructor
        · intro hg
          obtain ⟨μ, hμ⟩ := hmr hg
          exact ⟨_, by rw [hμ, Res.ok_bind]⟩
        · rintro ⟨_, hτ⟩
          obtain ⟨μ, hμ, -⟩ := Res.bind_eq_ok.1 hτ
          exact (hme μ hμ).1
      · obtain ⟨μ, hμ, he⟩ := Res.bind_eq_ok.1 hτ
        cases he
        exact Fml.toL_holds φ ⟨h.stor, fun y => h.env y, fun k => h.tx k,
          (hme μ hμ).2.of_heap rfl rfl⟩ hf2
    | selfBalance _ _ | saveNet _ =>
      simp only [UpdElem.inL, Bool.false_eq_true, false_and] at hf
  | .modal m P φ, _, _, _, _, hf => by
    obtain ⟨ω, rfl⟩ := Prog.reverts_eq hf
    cases m <;> simp only [holds, Prog.run, Stmt.run, bind, Except.bind, Modality.afterRun,
      Modality.after, Modality.onHalt, Fml.toL, LFml.holds, not_true_eq_false, ne_eq,
      Except.error.injEq, reduceCtorEq, not_false_eq_true, and_true]
  | .all x p φ, σ, τ, ρ, h, hf => by
    simp only [Fml.inL, Bool.and_eq_true, Bool.not_eq_true'] at hf
    have hx : x ∉ ρ.vars := by simpa only [List.contains_eq_mem, decide_eq_false_iff_not] using hf.1
    simp only [holds, Fml.toL, LFml.holds]
    exact forall_congr' fun v => imp_congr_right fun _ => Fml.toL_holds φ (h.free hx v) hf.2
  | .upd _ (_ :: _ :: _) _, _, _, _, _, hf | .havoc _, _, _, _, _, hf => by
    simp only [Fml.inL, Bool.false_eq_true] at hf

/-- `⊨ φ` is the formula with its updates pushed in, true in every state. -/
theorem Fml.valid_iff_toL (φ : Fml C) (hf : φ.inL Sym.empty = true) :
    (⊨ φ) ↔ ∀ σ, (φ.toL Sym.empty).holds σ :=
  forall_congr' fun σ => Fml.toL_holds φ (Rel.empty σ) hf

/-! ## What the storage reads after a write

`ReadWrite.lean` has the read at a written path and apart from it
(`find_save_diverge`).  Deciding needs the other two of mini-solkey's four
cases, and the `delete`: a read *above* a write finds a struct, a mapping or
an array, which is no word; a read *below* a written word finds nothing; a
read at or below a deleted location, before any key, finds the default of
what was there. -/

/-- A write at a nonempty path keeps the shape of what it writes into: a
struct stays a struct, an array an array of the same length and kind, a
mapping a mapping with the same default.  After `alice.age = 3;`, `alice` is
still a struct. -/
theorem saveLive_cons_shape {v new u : SVal} {s : Seg} {r : List Seg}
    (h : v.saveLive (s :: r) new = .ok u) :
    (∃ fs fs', v = .struct fs ∧ u = .struct fs') ∨
    (∃ es es' sh fx, v = .array es sh fx ∧ u = .array es' sh fx ∧ es'.length = es.length) ∨
    (∃ es es' d, v = .map es d ∧ u = .map es' d) := by
  cases v with
  | prim p => cases s <;> simp only [SVal.saveLive, reduceCtorEq] at h
  | struct fields =>
    cases s with
    | «at» _ => simp only [SVal.saveLive, reduceCtorEq] at h
    | field n =>
      simp only [SVal.saveLive] at h
      split at h
      · obtain ⟨_, _, he⟩ := Res.bind_eq_ok.1 h; cases he; exact .inl ⟨_, _, rfl, rfl⟩
      · simp only [reduceCtorEq] at h
  | array elems shadow fx =>
    cases s with
    | field _ => simp only [SVal.saveLive, reduceCtorEq] at h
    | «at» i =>
      simp only [SVal.saveLive] at h
      split at h
      · obtain ⟨_, _, he⟩ := Res.bind_eq_ok.1 h; cases he
        exact .inr (.inl ⟨_, _, _, _, rfl, rfl, List.length_set⟩)
      · simp only [reduceCtorEq] at h
  | map entries dflt =>
    cases s with
    | field _ => simp only [SVal.saveLive, reduceCtorEq] at h
    | «at» i =>
      simp only [SVal.saveLive] at h
      split at h <;>
        (obtain ⟨_, _, he⟩ := Res.bind_eq_ok.1 h; cases he; exact .inr (.inr ⟨_, _, _, rfl, rfl⟩))

/-- A write at a nonempty path returns a struct, an array or a mapping,
which reads as no word: after `alice.age = 3;`, `alice` is not a `uint`. -/
theorem save_cons_asValue {v new u : SVal} {s : Seg} {r : List Seg}
    (h : v.saveLive (s :: r) new = .ok u) : ∃ e, u.asValue = .error e := by
  rcases saveLive_cons_shape h with ⟨_, _, -, rfl⟩ | ⟨_, _, _, _, -, rfl, -⟩ | ⟨_, _, _, -, rfl⟩ <;>
    exact ⟨_, rfl⟩

/-- **A write passes through every location above it**: a write at `Q ++ R`
finds a location at `Q`, writes at `R` below it, and leaves that location
readable at `Q`.  Example: `alice.account.balance = 7;` passes through
`alice` and `alice.account`. -/
theorem save_through : ∀ {v new u : SVal} (Q R : List Seg),
    v.saveLive (Q ++ R) new = .ok u →
      ∃ w w', v.findLive Q = .ok w ∧ w.saveLive R new = .ok w' ∧ u.findLive Q = .ok w'
  | v, _, u, [], R, h => ⟨v, u, by cases v <;> rfl, h, by cases u <;> rfl⟩
  | v, new, u, s :: Q, R, h => by
    cases v with
    | prim p => cases s <;> simp only [List.cons_append, SVal.saveLive, reduceCtorEq] at h
    | struct fields =>
      cases s with
      | «at» _ => simp only [List.cons_append, SVal.saveLive, reduceCtorEq] at h
      | field n =>
        simp only [List.cons_append, SVal.saveLive] at h
        split at h
        · rename_i old hl
          obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h; cases he
          obtain ⟨w, w', h₁, h₂, h₃⟩ := save_through Q R hu
          exact ⟨w, w', by simp only [SVal.findLive, hl, h₁], h₂, by simp only [SVal.findLive,
              lookupBy_setBy_self, h₃]⟩
        · simp only [reduceCtorEq] at h
    | array elems shadow fx =>
      cases s with
      | field _ => simp only [List.cons_append, SVal.saveLive, reduceCtorEq] at h
      | «at» i =>
        simp only [List.cons_append, SVal.saveLive] at h
        split at h
        · rename_i hi
          obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h; cases he
          obtain ⟨w, w', h₁, h₂, h₃⟩ := save_through Q R hu
          refine ⟨w, w', by simp only [SVal.findLive, hi, and_self, ↓reduceDIte,
              List.get_eq_getElem, ← h₁], h₂, ?_⟩
          simp only [SVal.findLive, hi, List.length_set, and_self, ↓reduceDIte,
              List.get_eq_getElem, List.getElem_set_self, h₃]
        · simp only [reduceCtorEq] at h
    | map entries dflt =>
      cases s with
      | field _ => simp only [List.cons_append, SVal.saveLive, reduceCtorEq] at h
      | «at» i =>
        simp only [List.cons_append, SVal.saveLive] at h
        split at h <;> rename_i hl
        · obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h; cases he
          obtain ⟨w, w', h₁, h₂, h₃⟩ := save_through Q R hu
          exact ⟨w, w', by simp only [SVal.findLive, hl, h₁], h₂, by simp only [SVal.findLive,
              lookupBy_setBy_self, h₃]⟩
        · obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h; cases he
          obtain ⟨w, w', h₁, h₂, h₃⟩ := save_through Q R hu
          exact ⟨w, w', by simp only [SVal.findLive, hl, h₁], h₂, by simp only [SVal.findLive,
              lookupBy_setBy_self, h₃]⟩

/-- No segment is a `length`: the one field an array answers to, and the
one a program never writes. -/
def NoLen (ps : List Seg) : Prop := ∀ s ∈ ps, s ≠ .field "length"

/-- A run followed by a return returns when the run does. -/
theorem ex_ok_bind {α β : Type} {x : Res α} {f : α → β} :
    (∃ u, (x >>= fun a => .ok (f a)) = .ok u) ↔ ∃ a, x = .ok a := by
  cases x <;> simp only [bind, Except.bind, reduceCtorEq, exists_false, Except.ok.injEq, exists_eq']

/-- **A write succeeds where a read does**, `length` aside: `alice.age = 3;`
runs exactly where `alice.age` names a location. -/
theorem save_ok_iff_find_ok {new : SVal} : ∀ {v : SVal} {ps : List Seg}, NoLen ps →
    ((∃ u, v.saveLive ps new = .ok u) ↔ ∃ w, v.findLive ps = .ok w)
  | v, [], _ => by cases v <;> simp only [SVal.saveLive, Except.ok.injEq, exists_eq', SVal.findLive]
  | v, s :: ps, hn => by
    have hn' : NoLen ps := fun t ht => hn t (.tail _ ht)
    have hs : s ≠ .field "length" := hn s (.head _)
    cases v with
    | prim p => cases s <;> simp only [SVal.saveLive, reduceCtorEq, exists_false, SVal.findLive]
    | struct fields =>
      cases s with
      | «at» _ => simp only [SVal.saveLive, reduceCtorEq, exists_false, SVal.findLive]
      | field n =>
        simp only [SVal.saveLive, SVal.findLive]
        cases lookupBy n fields with
        | none => simp only [reduceCtorEq, exists_false]
        | some old => simp only [ex_ok_bind]; exact save_ok_iff_find_ok hn'
    | array elems shadow fx =>
      cases s with
      | field n =>
        have : n ≠ "length" := fun h => hs (by rw [h])
        simp only [SVal.saveLive, reduceCtorEq, exists_false, SVal.findLive]
      | «at» i =>
        simp only [SVal.saveLive, SVal.findLive]
        split
        · simp only [ex_ok_bind]; exact save_ok_iff_find_ok hn'
        · simp only [reduceCtorEq, exists_false]
    | map entries dflt =>
      cases s with
      | field _ => simp only [SVal.saveLive, reduceCtorEq, exists_false, SVal.findLive]
      | «at» i =>
        simp only [SVal.saveLive, SVal.findLive]
        cases lookupBy i entries <;> (simp only [ex_ok_bind]; exact save_ok_iff_find_ok hn')

/-- **Below a delete, at a member**: the member of the deleted value is the
deleted member.  After `delete alice;`, `alice.account` is the default of the
old `alice.account`; after `delete values;`, `values.length` is the default of
the old length, `0`; a fixed-size array has no `length` member before or
after. -/
theorem defaultOf_field (N : SVal) (f : Name) (more : List Seg) :
    N.defaultOf.findLive (.field f :: more) =
      N.findLive [.field f] >>= fun e => e.defaultOf.findLive more := by
  cases N with
  | prim p => cases p <;> rfl
  | struct fields =>
    simp only [SVal.defaultOf, SVal.findLive, lookupBy_defaultOfFields]
    cases lookupBy f fields <;> simp only [Option.map_none, bind, Except.bind, Option.map_some]
  | array elems shadow fx =>
    by_cases hf : f = "length"
    · subst hf
      cases fx <;> simp only [SVal.defaultOf, SVal.findLive, Bool.false_eq_true, ↓reduceIte,
          List.length_nil, Int.cast_ofNat_Int, bind, Except.bind]
    · cases fx <;> simp only [SVal.defaultOf, SVal.findLive, bind, Except.bind]
  | map _ _ => rfl

/-- **Below a delete, at a key**: a mapping keeps its entries; a fixed-size
array keeps its elements, each deleted in place; anything else has no key to
read (a dynamic array is emptied). -/
theorem defaultOf_key (N : SVal) (k : Int) (more : List Seg) (a : SVal) :
    N.defaultOf.findLive (.at k :: more) = .ok a ↔
      (isMapV N = true ∧ N.findLive (.at k :: more) = .ok a) ∨
      (isFixV N = true ∧ ∃ e, N.findLive [.at k] = .ok e ∧ e.defaultOf.findLive more = .ok a) := by
  cases N with
  | prim p => cases p <;> simp only [SVal.defaultOf, SVal.findLive, reduceCtorEq, isMapV,
      Bool.false_eq_true, and_self, isFixV, false_and, exists_false, or_self]
  | struct _ => simp only [SVal.defaultOf, SVal.findLive, reduceCtorEq, isMapV,
      Bool.false_eq_true, and_self, isFixV, false_and, exists_false, or_self]
  | array elems shadow fx =>
    cases fx
    · simp only [SVal.defaultOf, SVal.findLive, List.length_nil, Nat.not_lt_zero, and_false,
        ↓reduceDIte, reduceCtorEq, isMapV, Bool.false_eq_true, List.get_eq_getElem, false_and,
            isFixV, SVal.findLive_nil, or_self]
    · simp only [SVal.defaultOf, SVal.findLive, isMapV, isFixV, defaultOfElems_eq_map,
        List.length_map, List.get_eq_getElem, List.getElem_map, SVal.findLive_nil]
      by_cases hb : 0 ≤ k ∧ k.toNat < elems.length
      · simp only [hb, and_self, ↓reduceDIte, Bool.false_eq_true, false_and, Except.ok.injEq,
          exists_eq_left', true_and, false_or]
      · simp only [hb, ↓reduceDIte, reduceCtorEq, Bool.false_eq_true, and_self, false_and,
          exists_false, and_false, or_self]
  | map _ _ => simp only [SVal.defaultOf, isMapV, true_and, isFixV, Bool.false_eq_true, false_and,
      or_false]

/-- The default of a word reads as the word's default: `delete total;` then
`total` is `0`.  A struct, an array or a mapping reads as no word, before
and after. -/
theorem asValue_defaultOf (c : SVal) :
    c.defaultOf.asValue = c.asValue >>= fun x => .ok (zeroV x) := by
  cases c with
  | prim p => cases p <;> rfl
  | struct _ => rfl
  | array _ _ fx => cases fx <;> rfl
  | map _ _ => rfl

/-- **Below a delete, before any key**, a path reads the default of what it
read: after `delete alice.account;`, `alice.account.balance` is the default
of the old balance, and an array's `length` is `0`. -/
theorem find_defaultOf : ∀ (c : SVal) (rest : List Seg), rest.any Seg.isAt = false →
    c.defaultOf.findLive rest = c.findLive rest >>= fun w => .ok w.defaultOf
  | c, [], _ => by simp only [SVal.findLive_nil]; rfl
  | c, .at _ :: _, h => by simp only [List.any_cons, Seg.isAt, Bool.true_or,
      Bool.true_eq_false] at h
  | c, .field n :: r, h => by
    have hr : r.any Seg.isAt = false := by simpa only [List.any_eq_false, Seg.isAt,
        Bool.not_eq_true, List.any_cons, Bool.false_or] using h
    rw [defaultOf_field, show Seg.field n :: r = [Seg.field n] ++ r from rfl,
      SVal.findLive_append c [.field n] r, bind_assoc]
    congr 1; funext e
    exact find_defaultOf e r hr

/-! ## Comparing a write with a read

A write at `P` and a read at `Q` are compared segment by segment from the
root, mini-solkey's `LPath.cmp`: two members at once, two keys by a case on
their equality. -/

/-- A segment of a path, its key a term. -/
inductive SSeg where
  | field (f : Name)
  | key (k : LTerm)
  deriving Inhabited

/-- The segments of a path, root first. -/
def LPath.segs : LPath → List SSeg
  | .root r => [.field r]
  | .field q f => q.segs ++ [.field f]
  | .at q k => q.segs ++ [.key k]

/-- The segment is a key: the `[k]` of `balances[k]`. -/
def SSeg.isKey : SSeg → Bool
  | .field _ => false
  | .key _ => true

/-- Segments evaluated from the root. -/
def segsEval (σ : State) : List SSeg → Res (List Seg)
  | [] => .ok []
  | .field f :: r => segsEval σ r >>= fun rs => .ok (.field f :: rs)
  | .key k :: r => (k.eval σ >>= Value.asInt) >>= fun i => segsEval σ r >>= fun rs => .ok (.at i :: rs)

/-- Segments evaluate piece by piece: `alice.account` then `.balance`. -/
theorem segsEval_append (σ : State) : ∀ {xs ys : List SSeg} {a b : List Seg},
    segsEval σ xs = .ok a → segsEval σ ys = .ok b → segsEval σ (xs ++ ys) = .ok (a ++ b)
  | [], _, a, _, ha, hb => by cases ha; exact hb
  | .field f :: xs, _, a, _, ha, hb => by
    obtain ⟨a', ha', he⟩ := Res.bind_eq_ok.1 ha; cases he
    simp only [List.cons_append, segsEval, bind, Except.bind, segsEval_append σ ha' hb]
  | .key k :: xs, _, a, _, ha, hb => by
    obtain ⟨i, hi, ha⟩ := Res.bind_eq_ok.1 ha
    obtain ⟨a', ha', he⟩ := Res.bind_eq_ok.1 ha; cases he
    simp only [segsEval, hi, Res.ok_bind, segsEval_append σ ha' hb, List.cons_append]

/-- A path that evaluates has segments that do, to the same list. -/
theorem LPath.segs_eval (σ : State) : ∀ {q : LPath} {qs : List Seg},
    q.eval σ = .ok qs → segsEval σ q.segs = .ok qs
  | .root r, qs, h => by cases h; rfl
  | .field q f, qs, h => by
    obtain ⟨qs', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    exact segsEval_append σ (LPath.segs_eval σ h') rfl
  | .at q k, qs, h => by
    obtain ⟨qs', h', h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨i, hi, he⟩ := Res.bind_eq_ok.1 h; cases he
    exact segsEval_append σ (LPath.segs_eval σ h') (by simp only [segsEval, hi, Res.ok_bind])

/-- Evaluated segments have a key exactly where the terms do. -/
theorem segsEval_any (σ : State) : ∀ {xs : List SSeg} {a : List Seg},
    segsEval σ xs = .ok a → a.any Seg.isAt = xs.any SSeg.isKey
  | [], a, h => by cases h; rfl
  | .field f :: xs, a, h => by
    obtain ⟨a', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    simp only [List.any_cons, Seg.isAt, segsEval_any σ h', Bool.false_or, SSeg.isKey]
  | .key k :: xs, a, h => by
    obtain ⟨i, _, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨a', _, he⟩ := Res.bind_eq_ok.1 h; cases he
    simp only [List.any_cons, Seg.isAt, Bool.true_or, SSeg.isKey]

/-- How a read path `Q` stands to a written path `P`. -/
inductive PathRel where
  | eq
  | above
  /-- `Q` is below `P`, by the segments `rest`. -/
  | below (rest : List SSeg)
  | diverge
  deriving Inhabited

/-- What each relation says of the two paths. -/
def PathRel.Holds (σ : State) : PathRel → List Seg → List Seg → Prop
  | .eq, P, Q => Q = P
  | .above, P, Q => ∃ f r, P = Q ++ f :: r
  | .below rest, P, Q => ∃ f r, Q = P ++ f :: r ∧ segsEval σ rest = .ok (f :: r)
  | .diverge, P, Q => Close.Diverge P Q

/-- A value that depends on key equalities. -/
inductive CaseTree (α : Type) where
  | leaf (a : α)
  | ite (a b : LTerm) (t e : CaseTree α)

/-- The leaf a state selects. -/
def CaseTree.get {α : Type} (σ : State) : CaseTree α → α
  | .leaf a => a
  | .ite a b t e =>
    if keyEq (a.eval σ >>= Value.asInt) (b.eval σ >>= Value.asInt) then t.get σ else e.get σ

/-- A tree of terms as one term, its tests `kite`s. -/
def CaseTree.toTerm {α : Type} (f : α → LTerm) : CaseTree α → LTerm
  | .leaf a => f a
  | .ite a b t e => .kite a b (t.toTerm f) (e.toTerm f)

/-- Every test of the tree compares two integers. -/
def CaseTree.TestsOk {α : Type} (σ : State) : CaseTree α → Prop
  | .leaf _ => True
  | .ite a b t e => (∃ i, (a.eval σ >>= Value.asInt) = .ok i) ∧
      (∃ j, (b.eval σ >>= Value.asInt) = .ok j) ∧ t.TestsOk σ ∧ e.TestsOk σ

/-- The term of a tree reads what the selected leaf does, where its tests
compare integers. -/
theorem CaseTree.toTerm_eval {α : Type} (σ : State) (f : α → LTerm) :
    (t : CaseTree α) → t.TestsOk σ → (t.toTerm f).eval σ = (f (t.get σ)).eval σ
  | .leaf _, _ => rfl
  | .ite a b t e, ⟨⟨i, hi⟩, ⟨j, hj⟩, ht, he⟩ => by
    simp only [CaseTree.toTerm, LTerm.eval, CaseTree.get, hi, hj, keyEq, Res.ok_bind,
      decide_eq_true_eq]
    split
    · exact CaseTree.toTerm_eval σ f t ht
    · exact CaseTree.toTerm_eval σ f e he

/-- Two keys the terms alone compare, as KeY's `select(store(…))` does
before it splits: the same local, literal or value of the transaction is
the same key (`some true`),
two different integer literals are different ones (`some false`); anything
else is for the state to settle (`none`).  Not recursive, so the kernel
re-checking a reduction pays one comparison of names. -/
def keyCmp : LTerm → LTerm → Option Bool
  | .var x, .var y => if x = y then some true else none
  | .env k, .env k' => if k = k' then some true else none
  | .lit (.int a), .lit (.int b) => some (decide (a = b))
  | _, _ => none

/-- What `keyCmp` settles holds in every state where both keys are integers. -/
theorem keyCmp_spec {σ : State} {i j : LTerm} {c : Bool} {a b : Int}
    (hk : keyCmp i j = some c) (ha : (i.eval σ >>= Value.asInt) = .ok a)
    (hb : (j.eval σ >>= Value.asInt) = .ok b) : decide (a = b) = c := by
  unfold keyCmp at hk
  split at hk
  · split at hk
    · cases hk
      subst_vars
      rw [ha] at hb
      cases hb
      simp only [decide_true]
    · cases hk
  · split at hk
    · cases hk
      subst_vars
      rw [ha] at hb
      cases hb
      simp only [decide_true]
    · cases hk
  · cases hk
    simp only [LTerm.eval, Res.ok_bind, Value.asInt] at ha hb
    cases ha
    cases hb
    rfl
  · cases hk

/-- `cmpSegs P Q`: how the read `Q` stands to the write `P`.

Example: `balances[j]` against `balances[k]` is `ite j k eq diverge`, and
`balances[k]` against `balances[k]` is `eq` (`keyCmp`). -/
def cmpSegs : List SSeg → List SSeg → CaseTree PathRel
  | [], [] => .leaf .eq
  | [], q => .leaf (.below q)
  | _, [] => .leaf .above
  | .field f :: p, .field g :: q => if f = g then cmpSegs p q else .leaf .diverge
  | .key i :: p, .key j :: q => match keyCmp i j with
    | some true => cmpSegs p q
    | some false => .leaf .diverge
    | none => .ite i j (cmpSegs p q) (.leaf .diverge)
  | .field _ :: _, .key _ :: _ | .key _ :: _, .field _ :: _ => .leaf .diverge

/-- A common first segment keeps the relation. -/
theorem PathRel.Holds.cons {σ : State} {r : PathRel} {P Q : List Seg} (x : Seg)
    (h : r.Holds σ P Q) : r.Holds σ (x :: P) (x :: Q) := by
  cases r with
  | eq => simp_all only [Holds]
  | above => obtain ⟨f, t, h⟩ := h; exact ⟨f, t, by simp only [h, List.cons_append]⟩
  | below k => obtain ⟨f, t, h, hk⟩ := h; exact ⟨f, t, by simp only [h, List.cons_append], hk⟩
  | diverge => exact .inr h

/-- **The comparison is right**: in a state where both paths evaluate, it
selects the relation they are in.  Example: for the write
`balances[j] = 6;` and the read `balances[k]`, `eq` where `k = j`, `diverge`
elsewhere. -/
theorem cmpSegs_holds (σ : State) : ∀ (P Q : List SSeg) {ps qs : List Seg},
    segsEval σ P = .ok ps → segsEval σ Q = .ok qs → ((cmpSegs P Q).get σ).Holds σ ps qs
  | [], [], _, _, hp, hq => by cases hp; cases hq; rfl
  | [], y :: ys, ps, qs, hp, hq => by
    cases hp
    have hq₀ := hq
    revert hq hq₀
    cases y with
    | field g =>
      intro hq hq₀
      obtain ⟨a, _, he⟩ := Res.bind_eq_ok.1 hq; cases he
      exact ⟨_, _, rfl, hq₀⟩
    | key j =>
      intro hq hq₀
      obtain ⟨i, _, hq⟩ := Res.bind_eq_ok.1 hq
      obtain ⟨a, _, he⟩ := Res.bind_eq_ok.1 hq; cases he
      exact ⟨_, _, rfl, hq₀⟩
  | x :: xs, [], ps, qs, hp, hq => by
    cases hq
    cases x with
    | field g =>
      obtain ⟨a, _, he⟩ := Res.bind_eq_ok.1 hp; cases he
      exact ⟨_, _, rfl⟩
    | key j =>
      obtain ⟨i, _, hp⟩ := Res.bind_eq_ok.1 hp
      obtain ⟨a, _, he⟩ := Res.bind_eq_ok.1 hp; cases he
      exact ⟨_, _, rfl⟩
  | .field f :: xs, .field g :: ys, ps, qs, hp, hq => by
    obtain ⟨a, ha, he⟩ := Res.bind_eq_ok.1 hp; cases he
    obtain ⟨b, hb, he⟩ := Res.bind_eq_ok.1 hq; cases he
    by_cases hfg : f = g
    · subst hfg
      simpa only [cmpSegs, ↓reduceIte] using (cmpSegs_holds σ xs ys ha hb).cons (.field f)
    · simp only [cmpSegs, hfg, if_false, CaseTree.get]
      exact .inl (by simpa only [ne_eq, Seg.field.injEq] using hfg)
  | .key i :: xs, .key j :: ys, ps, qs, hp, hq => by
    obtain ⟨a, ha, hp⟩ := Res.bind_eq_ok.1 hp
    obtain ⟨as, has, he⟩ := Res.bind_eq_ok.1 hp; cases he
    obtain ⟨b, hb, hq⟩ := Res.bind_eq_ok.1 hq
    obtain ⟨bs, hbs, he⟩ := Res.bind_eq_ok.1 hq; cases he
    rcases hk : keyCmp i j with _ | _ | _
    · simp only [cmpSegs, hk, CaseTree.get, ha, hb, keyEq]
      by_cases hab : a = b
      · subst hab
        simpa only [decide_true, ↓reduceIte] using (cmpSegs_holds σ xs ys has hbs).cons (.at a)
      · simp only [hab, decide_false, Bool.false_eq_true, if_false]
        exact .inl (by simpa only [ne_eq, Seg.at.injEq] using hab)
    · have hab : a ≠ b := by simpa only [ne_eq, decide_eq_false_iff_not] using keyCmp_spec hk ha hb
      simp only [cmpSegs, hk, CaseTree.get]
      exact .inl (by simpa only [ne_eq, Seg.at.injEq] using hab)
    · have hab : a = b := by simpa only [decide_eq_true_eq] using keyCmp_spec hk ha hb
      subst hab
      simpa only [cmpSegs, hk] using (cmpSegs_holds σ xs ys has hbs).cons (.at a)
  | .field f :: xs, .key j :: ys, ps, qs, hp, hq => by
    obtain ⟨a, ha, he⟩ := Res.bind_eq_ok.1 hp; cases he
    obtain ⟨b, hb, hq⟩ := Res.bind_eq_ok.1 hq
    obtain ⟨bs, hbs, he⟩ := Res.bind_eq_ok.1 hq; cases he
    exact .inl (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
  | .key i :: xs, .field g :: ys, ps, qs, hp, hq => by
    obtain ⟨a, ha, hp⟩ := Res.bind_eq_ok.1 hp
    obtain ⟨as, has, he⟩ := Res.bind_eq_ok.1 hp; cases he
    obtain ⟨b, hb, he⟩ := Res.bind_eq_ok.1 hq; cases he
    exact .inl (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])

/-- The comparison of two paths that evaluate compares integers only. -/
theorem cmpSegs_testsOk (σ : State) : ∀ (P Q : List SSeg) {ps qs : List Seg},
    segsEval σ P = .ok ps → segsEval σ Q = .ok qs → (cmpSegs P Q).TestsOk σ
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, _, _ => trivial
  | .field _ :: _, [], _, _, _, _ | .key _ :: _, [], _, _, _, _ => trivial
  | .field f :: xs, .field g :: ys, _, _, hp, hq => by
    obtain ⟨_, ha, -⟩ := Res.bind_eq_ok.1 hp
    obtain ⟨_, hb, -⟩ := Res.bind_eq_ok.1 hq
    simp only [cmpSegs]
    split
    · exact cmpSegs_testsOk σ xs ys ha hb
    · trivial
  | .key i :: xs, .key j :: ys, _, _, hp, hq => by
    obtain ⟨a, ha, hp⟩ := Res.bind_eq_ok.1 hp
    obtain ⟨_, has, -⟩ := Res.bind_eq_ok.1 hp
    obtain ⟨b, hb, hq⟩ := Res.bind_eq_ok.1 hq
    obtain ⟨_, hbs, -⟩ := Res.bind_eq_ok.1 hq
    simp only [cmpSegs]
    split
    · exact cmpSegs_testsOk σ xs ys has hbs
    · trivial
    · exact ⟨⟨a, ha⟩, ⟨b, hb⟩, cmpSegs_testsOk σ xs ys has hbs, trivial⟩
  | .field _ :: _, .key _ :: _, _, _, _, _ => trivial
  | .key _ :: _, .field _ :: _, _, _, _, _ => trivial

/-! ## Eliminating the reads of writes

`find(s, Q)` with writes in `s` becomes a case tree whose leaves read the
initial storage only.  Each read is guarded by what makes it return: the
writes below it succeed (`LStor.okE`) and its path evaluates.  Under the
guard, `readU` and `hasU` peel off one write at a time, comparing paths. -/

/-- The path has no `length` segment. -/
def LPath.noLen : LPath → Bool
  | .root r => r != "length"
  | .field q f => q.noLen && f != "length"
  | .at q _ => q.noLen

/-- The leaf of a read after a write of `w`: the value at the written path,
none above it (a struct is no word) or below it (a word has no members), the
old read apart from it. -/
def saveLeaf (w old : LTerm) : PathRel → LTerm
  | .eq => w
  | .above | .below _ => .err
  | .diverge => old

/-- A read below a deleted location, `rest` below `q`, from the root down:
through a member, what the member of the deleted value has; at a key, the old
read (`atMap`) where the location above the key is a mapping, which `delete`
leaves alone (`guard .map`); the same one key further down where it is a
fixed-size array, whose elements `delete` resets in place (`guard .fixed`);
nothing where it is anything else (a dynamic array is emptied).  With every
key passed, the default of the old read (`atEnd`).  After `delete ledger;`,
`ledger.balances[k]` is the old entry; after `delete grid;` (`uint[2][3]`),
`grid[i][j]` is `0`. -/
def delBelow (atMap atEnd : LTerm) (guard : KShape → LPath → LTerm) : LPath → List SSeg → LTerm
  | q, .field f :: r => delBelow atMap atEnd guard (q.field f) r
  | q, .key k :: r => .orElse (.seq (guard .map q) atMap)
      (.seq (guard .fixed q) (delBelow atMap atEnd guard (q.at k) r))
  | _, [] => atEnd

/-- The leaf of a read after a `delete` of `P`: the default of the old word
at the path, and below it as `delBelow` walks it. -/
def delLeaf (old : LTerm) (P : LPath) (guard : KShape → LPath → LTerm) : PathRel → LTerm
  | .eq => .zero old
  | .below rest => delBelow old (.zero old) guard P rest
  | .above => .err
  | .diverge => old

/-- Whether a location is there after a write. -/
def saveHas (old : LTerm) : PathRel → LTerm
  | .eq | .above => .lit (.bool true)
  | .below _ => .err
  | .diverge => old

/-- Whether a location is there after a `delete`: through members as before,
through keys as `delBelow` says. -/
def delHas (old : LTerm) (P : LPath) (guard : KShape → LPath → LTerm) : PathRel → LTerm
  | .eq | .above => .lit (.bool true)
  | .below rest => delBelow old old guard P rest
  | .diverge => old

/-- Whether a mapping is there after a write: a write keeps the shape of
every location above it. -/
def saveMap (old : LTerm) : PathRel → LTerm
  | .eq | .below _ => .err
  | .above | .diverge => old

/-- Whether a mapping (a fixed-size array) is there after a `delete`: the
default of a value has its shape. -/
def delMap (old : LTerm) (P : LPath) (guard : KShape → LPath → LTerm) : PathRel → LTerm
  | .eq | .above | .diverge => old
  | .below rest => delBelow old old guard P rest

/-- The length of an array's default: a fixed-size array keeps it (`fixed`
returns where it is one), a dynamic one is emptied.  `delete values;` leaves
`values.length` at `0`, `delete fixedValues;` at `3`. -/
def lenEnd (old fixed : LTerm) : LTerm := .orElse (.seq fixed old) (.seq old (.lit (.int 0)))

/-- The length at `Q` after a `delete` of `P`: its default's where `Q` is
`P`, as `delBelow` walks it below `P`, the old one above or apart. -/
def delLen (old atEnd : LTerm) (P : LPath) (guard : KShape → LPath → LTerm) : PathRel → LTerm
  | .eq => atEnd
  | .above | .diverge => old
  | .below rest => delBelow old atEnd guard P rest

/-- The length after a `push`, unchecked (`bool` arithmetic is not
range-checked): a storage array's length has no bound. -/
def lenSucc (L : LTerm) : LTerm := .binop .add .bool L (.lit (.int 1))

/-- The length after a `pop`, unchecked as `lenSucc`. -/
def lenPred (L : LTerm) : LTerm := .binop .sub .bool L (.lit (.int 1))

/-- The default word of a primitive type: what `values.push();` appends. -/
def dfltV : PrimTy → Value
  | .bool => .bool false
  | .uint | .int => .int 0

/-- Returns where the operation on an array of length `L` does: a push
wherever there is an array, a `pop` where it is not empty. -/
def arrOk : AOp → LTerm → LTerm
  | .push, L | .slot _, L => .seq L (.lit (.bool true))
  | .pop _, L => .ite (.binop .lt .uint (.lit (.int 0)) L) (.lit (.bool true)) .err

/-- The slot an operation appends, at an index `k` against the old length
`L`: the word `w` or a primitive default at `k = L` (`atNew`, nothing below a
word), the old element elsewhere.  A `pop` leaves nothing at `L - 1`.  Below
a `push()` of a struct or an array the read itself (`opq`): the closer types
it whole, the slot and the elements alike (`Facts.slotTy`). -/
def arrKey (op : AOp) (L k old opq : LTerm) (atNew : LTerm) : LTerm :=
  match op with
  | .push | .slot (.prim _) => .kite k L atNew old
  | .slot (.ref _) => opq
  | .pop _ => .kite k (lenPred L) .err old

/-- The leaf of a read after an operation on the array at `P`: no word at or
above the array; below it, by `arrKey`; the old read apart from it. -/
def arrRead (op : AOp) (w L old opq : LTerm) (slot : List SSeg → LTerm) : PathRel → LTerm
  | .eq | .above => .err
  | .diverge => old
  | .below (.key k :: rest) =>
    match op with
    | .slot (.ref _) => .kite k L (slot rest) old
    | _ => arrKey op L k old opq (match op with
      | .push => if rest.isEmpty then w else .err
      | .slot (.prim p) => if rest.isEmpty then .lit (dfltV p) else .err
      | _ => .err)
  | .below _ => opq

/-- `true` where `0 ≤ k ≤ L`, halting elsewhere: an index of an array of
length `L + 1`. -/
def inRange (k L : LTerm) : LTerm :=
  .ite (.binop .and .bool (.binop .le .uint (.lit (.int 0)) k) (.binop .le .uint k L))
    (.lit (.bool true)) .err

/-- Whether a location is there after an operation on an array: an element
of a pushed struct or array at an index up to the old length. -/
def arrHas (op : AOp) (L old opq : LTerm) : PathRel → LTerm
  | .eq | .above => .lit (.bool true)
  | .diverge => old
  | .below (.key k :: rest) =>
    match op with
    | .slot (.ref _) => if rest.isEmpty then inRange k L else opq
    | _ => arrKey op L k old opq (if rest.isEmpty then .lit (.bool true) else .err)
  | .below _ => opq

/-- The length at `Q` after an operation on the array at `P`: one more or
one less at `P`, the old one above or apart. -/
def arrLength (op : AOp) (L old opq : LTerm) : PathRel → LTerm
  | .eq => match op with
    | .push | .slot _ => lenSucc L
    | .pop _ => lenPred L
  | .above | .diverge => old
  | .below (.key k :: _) => arrKey op L k old opq .err
  | .below _ => opq

/-- Whether a mapping (a fixed-size array) is at `Q` after an operation on
an array: the shapes at and above it stay. -/
def arrMap (op : AOp) (L old opq : LTerm) : PathRel → LTerm
  | .eq | .above | .diverge => old
  | .below (.key k :: _) => arrKey op L k old opq .err
  | .below _ => opq

/-- A test that returns `true` where `t` returns and `false` where it halts. -/
def isT (t : LTerm) : LTerm := .orElse (.seq t (.lit (.bool true))) (.lit (.bool false))

/-- A read below a copy, the segments `pre` walked: at a key, the read
itself (`opq`) where the source has a mapping there (a mapping met in both
keeps the target's entries; a copy of a well-typed program has none); with
no key left, what the source has (`F`). -/
def copyKeys (srcMap : List SSeg → LTerm) (opq : LTerm) (F : List SSeg → LTerm) :
    List SSeg → List SSeg → LTerm
  | pre, [] => F pre
  | pre, .field f :: r => copyKeys srcMap opq F (pre ++ [.field f]) r
  | pre, .key k :: r => .ite (isT (srcMap pre)) opq (copyKeys srcMap opq F (pre ++ [.key k]) r)

/-- The leaf of a read after a copy over `P`: at and below `P`, what the
source has there (`copyKeys`); the old read apart. -/
def copyLeaf (atEq aboveV old opq : LTerm) (srcMap F : List SSeg → LTerm) : PathRel → LTerm
  | .eq => atEq
  | .above => aboveV
  | .diverge => old
  | .below rest => copyKeys srcMap opq F [] rest

/-- The path extended by the segments `rest`. -/
def LPath.addSegs : LPath → List SSeg → LPath
  | q, [] => q
  | q, .field f :: r => LPath.addSegs (q.field f) r
  | q, .key k :: r => LPath.addSegs (q.at k) r

/-- The path extended by the members `rest` starts with, up to its first
key: `alice` and `[account, balances, k]` make `alice.account.balances`. -/
def LPath.addFields : LPath → List SSeg → LPath
  | q, .field f :: r => LPath.addFields (q.field f) r
  | q, _ => q

mutual

/-- Every read of a write eliminated. -/
def LTerm.elim : LTerm → LTerm
  | .lit v => .lit v
  | .var x => .var x
  | .binop op p a b => .binop op p a.elim b.elim
  | .unop op p a => .unop op p a.elim
  | .ite c a b => .ite c.elim a.elim b.elim
  | .find s q => .seq s.okE (.seq (.pok q.elim) (s.readU q.elim))
  | .has s q => .seq s.okE (.seq (.pok q.elim) (s.hasU q.elim))
  | .kmap sh s q => .seq s.okE (.seq (.pok q.elim) (s.mapU sh q.elim))
  | .len s q => .seq s.okE (.seq (.pok q.elim) (s.lenU q.elim))
  | .sok s => s.okE
  | .pok q => .pok q.elim
  | .seq d a => .seq d.elim a.elim
  | .orElse a b => .orElse a.elim b.elim
  | .kite a b t e => .kite a.elim b.elim t.elim e.elim
  | .zero a => .zero a.elim
  | .err => .err
  | .env k => .env k
  | .findP s q => .findP s q.elim
  | .cpok s q => .cpok s q
termination_by structural t => t

/-- A path with the reads in its keys eliminated: `people[balances[a]]`. -/
def LPath.elim : LPath → LPath
  | .root r => .root r
  | .field q f => .field q.elim f
  | .at q k => .at q.elim k.elim
termination_by structural q => q

/-- Returns exactly when the writes of `s` succeed. -/
def LStor.okE : LStor → LTerm
  | .init => .lit (.bool true)
  | .save s q w =>
    if q.noLen then .seq s.okE (.seq w.elim (.seq (.pok q.elim) (s.hasU q.elim)))
    else .sok (.save s q w)
  | .del s q =>
    if q.noLen then .seq s.okE (.seq (.pok q.elim) (s.hasU q.elim))
    else .sok (.del s q)
  | .arr op s q w =>
    if q.noLen then .seq s.okE (.seq w.elim (.seq (.pok q.elim) (arrOk op (s.lenU q.elim))))
    else .sok (.arr op s q w)
  | .copy s q src sq =>
    if q.noLen then .seq src.okE (.seq (.pok sq.elim) (.seq (src.hasU sq.elim)
      (.seq s.okE (.seq (.pok q.elim) (s.hasU q.elim)))))
    else .sok (.copy s q src sq)
  | .view m i => .sok (.view m i)
termination_by structural s => s

/-- The word at `Q` in `s`, where `s` and `Q` return. -/
def LStor.readU : LStor → LPath → LTerm
  | .init, Q => .find .init Q
  | .save s P w, Q => (cmpSegs P.elim.segs Q.segs).toTerm (saveLeaf w.elim (s.readU Q))
  | .del s P, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (delLeaf (s.readU Q) P.elim fun sh q => s.mapU sh q)
  | .arr op s P w, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (arrRead op w.elim (s.lenU P.elim) (s.readU Q) (.find (.arr op s P w) Q)
        fun rest => s.slotU P.elim rest (.find (.arr op s P w) Q))
  | .copy s P src SQ, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (copyLeaf (src.readU SQ.elim) .err (s.readU Q) (.find (.copy s P src SQ) Q)
        (fun pre => src.mapU .map (SQ.elim.addSegs pre)) fun rest => src.readU (SQ.elim.addSegs rest))
  | .view m i, Q => .find (.view m i) Q
termination_by structural s => s

/-- What the slot a `push()` of a struct or an array takes holds at `rest`,
the array at `P` in `s` (`pushSlot`: the first slot past the end, recycled):
after a `pop` at `P`, the element it popped, cleared (as below a `delete`)
or kept; after a `delete` of a dynamic array at `P`, its old first element,
cleared, where it had one.  Elsewhere the read itself (`opq`). -/
def LStor.slotU : LStor → LPath → List SSeg → LTerm → LTerm
  | .arr (.pop keep) s P' _, P, rest, opq =>
    if P'.elim == P then
      if keep then s.readU ((P.at (lenPred (s.lenU P))).addSegs rest)
      else delLeaf (s.readU ((P.at (lenPred (s.lenU P))).addSegs rest)) (P.at (lenPred (s.lenU P)))
        (fun sh q => s.mapU sh q) (if rest.isEmpty then .eq else .below rest)
    else opq
  | .del s P', P, rest, opq =>
    if P'.elim == P then
      .ite (isT (s.mapU .fixed P)) opq
        (.kite (s.lenU P) (.lit (.int 0)) opq
          (delLeaf (s.readU ((P.at (.lit (.int 0))).addSegs rest)) (P.at (.lit (.int 0)))
            (fun sh q => s.mapU sh q) (if rest.isEmpty then .eq else .below rest)))
    else opq
  | .init, _, _, opq | .save .., _, _, opq | .arr .push .., _, _, opq
  | .arr (.slot _) .., _, _, opq | .copy .., _, _, opq | .view .., _, _, opq => opq
termination_by structural s => s

/-- Whether `Q` names a location of `s`, where `s` and `Q` return. -/
def LStor.hasU : LStor → LPath → LTerm
  | .init, Q => .has .init Q
  | .save s P _, Q => (cmpSegs P.elim.segs Q.segs).toTerm (saveHas (s.hasU Q))
  | .del s P, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (delHas (s.hasU Q) P.elim fun sh q => s.mapU sh q)
  | .arr op s P w, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (arrHas op (s.lenU P.elim) (s.hasU Q) (.has (.arr op s P w) Q))
  | .copy s P src SQ, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (copyLeaf (.lit (.bool true)) (.lit (.bool true)) (s.hasU Q) (.has (.copy s P src SQ) Q)
        (fun pre => src.mapU .map (SQ.elim.addSegs pre)) fun rest => src.hasU (SQ.elim.addSegs rest))
  | .view m i, Q => .has (.view m i) Q
termination_by structural s => s

/-- The length of the array at `Q` in `s`, where `s` and `Q` return: a
write keeps the length of every array above it, as it keeps its shape. -/
def LStor.lenU : LStor → LPath → LTerm
  | .init, Q => .len .init Q
  | .save s P _, Q => (cmpSegs P.elim.segs Q.segs).toTerm (saveMap (s.lenU Q))
  | .del s P, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (delLen (s.lenU Q) (lenEnd (s.lenU Q) (s.mapU .fixed Q)) P.elim fun sh q => s.mapU sh q)
  | .arr op s P w, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (arrLength op (s.lenU P.elim) (s.lenU Q) (.len (.arr op s P w) Q))
  | .copy s P src SQ, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (copyLeaf (src.lenU SQ.elim) (s.lenU Q) (s.lenU Q) (.len (.copy s P src SQ) Q)
        (fun pre => src.mapU .map (SQ.elim.addSegs pre)) fun rest => src.lenU (SQ.elim.addSegs rest))
  | .view m i, Q => .len (.view m i) Q
termination_by structural s => s

/-- Whether `Q` names a mapping (`sh = .map`) or a fixed-size array
(`.fixed`) of `s`, where `s` and `Q` return. -/
def LStor.mapU (sh : KShape) : LStor → LPath → LTerm
  | .init, Q => .kmap sh .init Q
  | .save s P _, Q => (cmpSegs P.elim.segs Q.segs).toTerm (saveMap (s.mapU sh Q))
  | .del s P, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (delMap (s.mapU sh Q) P.elim fun sh' q => s.mapU sh' q)
  | .arr op s P w, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (arrMap op (s.lenU P.elim) (s.mapU sh Q) (.kmap sh (.arr op s P w) Q))
  | .copy s P src SQ, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (copyLeaf (src.mapU sh SQ.elim) (s.mapU sh Q) (s.mapU sh Q) (.kmap sh (.copy s P src SQ) Q)
        (fun pre => src.mapU .map (SQ.elim.addSegs pre)) fun rest => src.mapU sh (SQ.elim.addSegs rest))
  | .view m i, Q => .kmap sh (.view m i) Q
termination_by structural s => s

end

/-! ### The elimination as compiled code

The elimination's `.arr` cases pass the old length and the old value to
their leaf as strict arguments: two recursive calls on the same storage, so
compiled code (`Derive.leafFits`, run through `evalExpr`, which heeds no
heartbeats) does `2^k` calls for `k` operations on arrays where the term it
builds is small; twelve pushes alternating between two arrays took 106 s.
The `F` copies below differ only there (`CaseTree.toTermLazy`): a leaf
computes what it reads, 7 ms on the same leaf.  `@[csimp]` makes compiled
code run them; the kernel and every proof see the definitions above. -/

/-- The relations at which an operation on an array reads the old length
(`arrKey`'s `L`). -/
def PathRel.needsLen : PathRel → Bool
  | .eq | .below _ => true
  | .above | .diverge => false

/-- The relations at which the leaf of an operation on an array reads the
old value: all but the array itself. -/
def PathRel.needsOld : PathRel → Bool
  | .eq => false
  | .above | .below _ | .diverge => true

/-- `t.toTerm (f L old)`, where a tree that is one leaf `r` computes `L`
and `old` only where `r` reads them (`needsLen`, `nO`): compiled code
evaluates arguments strictly, and the two are recursive calls on the same
storage. -/
@[inline] def CaseTree.toTermLazy (nO : PathRel → Bool) (t : CaseTree PathRel)
    (L old : Unit → LTerm) (f : LTerm → LTerm → PathRel → LTerm) : LTerm :=
  match t with
  | .leaf r => f (if r.needsLen then L () else .err) (if nO r then old () else .err) r
  | t => t.toTerm (f (L ()) (old ()))

/-- The lazy tree is the tree, where the leaf function ignores what it
is not given. -/
theorem CaseTree.toTermLazy_eq (nO : PathRel → Bool) (t : CaseTree PathRel) (L old : LTerm)
    (f : LTerm → LTerm → PathRel → LTerm)
    (hf : ∀ r, f (if r.needsLen then L else .err) (if nO r then old else .err) r = f L old r) :
    t.toTermLazy nO (fun _ => L) (fun _ => old) f = t.toTerm (f L old) := by
  cases t with
  | leaf r => exact hf r
  | ite => rfl

mutual

/-- `LTerm.elim` as compiled code runs it (`LTerm.elim_csimp`). -/
def LTerm.elimF : LTerm → LTerm
  | .lit v => .lit v
  | .var x => .var x
  | .binop op p a b => .binop op p a.elimF b.elimF
  | .unop op p a => .unop op p a.elimF
  | .ite c a b => .ite c.elimF a.elimF b.elimF
  | .find s q => .seq s.okEF (.seq (.pok q.elimF) (s.readUF q.elimF))
  | .has s q => .seq s.okEF (.seq (.pok q.elimF) (s.hasUF q.elimF))
  | .kmap sh s q => .seq s.okEF (.seq (.pok q.elimF) (s.mapUF sh q.elimF))
  | .len s q => .seq s.okEF (.seq (.pok q.elimF) (s.lenUF q.elimF))
  | .sok s => s.okEF
  | .pok q => .pok q.elimF
  | .seq d a => .seq d.elimF a.elimF
  | .orElse a b => .orElse a.elimF b.elimF
  | .kite a b t e => .kite a.elimF b.elimF t.elimF e.elimF
  | .zero a => .zero a.elimF
  | .err => .err
  | .env k => .env k
  | .findP s q => .findP s q.elimF
  | .cpok s q => .cpok s q
termination_by structural t => t

/-- `LPath.elim` as compiled code runs it. -/
def LPath.elimF : LPath → LPath
  | .root r => .root r
  | .field q f => .field q.elimF f
  | .at q k => .at q.elimF k.elimF
termination_by structural q => q

/-- `LStor.okE` as compiled code runs it. -/
def LStor.okEF : LStor → LTerm
  | .init => .lit (.bool true)
  | .save s q w =>
    if q.noLen then .seq s.okEF (.seq w.elimF (.seq (.pok q.elimF) (s.hasUF q.elimF)))
    else .sok (.save s q w)
  | .del s q =>
    if q.noLen then .seq s.okEF (.seq (.pok q.elimF) (s.hasUF q.elimF))
    else .sok (.del s q)
  | .arr op s q w =>
    if q.noLen then .seq s.okEF (.seq w.elimF (.seq (.pok q.elimF) (arrOk op (s.lenUF q.elimF))))
    else .sok (.arr op s q w)
  | .copy s q src sq =>
    if q.noLen then .seq src.okEF (.seq (.pok sq.elimF) (.seq (src.hasUF sq.elimF)
      (.seq s.okEF (.seq (.pok q.elimF) (s.hasUF q.elimF)))))
    else .sok (.copy s q src sq)
  | .view m i => .sok (.view m i)
termination_by structural s => s

/-- `LStor.readU` as compiled code runs it: an operation on an array reads
the old length and value only where the relation needs them. -/
def LStor.readUF : LStor → LPath → LTerm
  | .init, Q => .find .init Q
  | .save s P w, Q => (cmpSegs P.elimF.segs Q.segs).toTerm (saveLeaf w.elimF (s.readUF Q))
  | .del s P, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (delLeaf (s.readUF Q) P.elimF fun sh q => s.mapUF sh q)
  | .arr op s P w, Q =>
    let Pe := P.elimF
    (cmpSegs Pe.segs Q.segs).toTermLazy PathRel.needsOld (fun _ => s.lenUF Pe) (fun _ => s.readUF Q)
      fun L old => arrRead op w.elimF L old (.find (.arr op s P w) Q)
        fun rest => s.slotUF Pe rest (.find (.arr op s P w) Q)
  | .copy s P src SQ, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (copyLeaf (src.readUF SQ.elimF) .err (s.readUF Q) (.find (.copy s P src SQ) Q)
        (fun pre => src.mapUF .map (SQ.elimF.addSegs pre))
        fun rest => src.readUF (SQ.elimF.addSegs rest))
  | .view m i, Q => .find (.view m i) Q
termination_by structural s => s

/-- `LStor.slotU` as compiled code runs it. -/
def LStor.slotUF : LStor → LPath → List SSeg → LTerm → LTerm
  | .arr (.pop keep) s P' _, P, rest, opq =>
    if P'.elimF == P then
      if keep then s.readUF ((P.at (lenPred (s.lenUF P))).addSegs rest)
      else delLeaf (s.readUF ((P.at (lenPred (s.lenUF P))).addSegs rest))
        (P.at (lenPred (s.lenUF P)))
        (fun sh q => s.mapUF sh q) (if rest.isEmpty then .eq else .below rest)
    else opq
  | .del s P', P, rest, opq =>
    if P'.elimF == P then
      .ite (isT (s.mapUF .fixed P)) opq
        (.kite (s.lenUF P) (.lit (.int 0)) opq
          (delLeaf (s.readUF ((P.at (.lit (.int 0))).addSegs rest)) (P.at (.lit (.int 0)))
            (fun sh q => s.mapUF sh q) (if rest.isEmpty then .eq else .below rest)))
    else opq
  | .init, _, _, opq | .save .., _, _, opq | .arr .push .., _, _, opq
  | .arr (.slot _) .., _, _, opq | .copy .., _, _, opq | .view .., _, _, opq => opq
termination_by structural s => s

/-- `LStor.hasU` as compiled code runs it. -/
def LStor.hasUF : LStor → LPath → LTerm
  | .init, Q => .has .init Q
  | .save s P _, Q => (cmpSegs P.elimF.segs Q.segs).toTerm (saveHas (s.hasUF Q))
  | .del s P, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (delHas (s.hasUF Q) P.elimF fun sh q => s.mapUF sh q)
  | .arr op s P w, Q =>
    let Pe := P.elimF
    (cmpSegs Pe.segs Q.segs).toTermLazy PathRel.needsOld (fun _ => s.lenUF Pe) (fun _ => s.hasUF Q)
      fun L old => arrHas op L old (.has (.arr op s P w) Q)
  | .copy s P src SQ, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (copyLeaf (.lit (.bool true)) (.lit (.bool true)) (s.hasUF Q) (.has (.copy s P src SQ) Q)
        (fun pre => src.mapUF .map (SQ.elimF.addSegs pre))
        fun rest => src.hasUF (SQ.elimF.addSegs rest))
  | .view m i, Q => .has (.view m i) Q
termination_by structural s => s

/-- `LStor.lenU` as compiled code runs it. -/
def LStor.lenUF : LStor → LPath → LTerm
  | .init, Q => .len .init Q
  | .save s P _, Q => (cmpSegs P.elimF.segs Q.segs).toTerm (saveMap (s.lenUF Q))
  | .del s P, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (delLen (s.lenUF Q) (lenEnd (s.lenUF Q) (s.mapUF .fixed Q)) P.elimF fun sh q => s.mapUF sh q)
  | .arr op s P w, Q =>
    let Pe := P.elimF
    (cmpSegs Pe.segs Q.segs).toTermLazy PathRel.needsOld (fun _ => s.lenUF Pe) (fun _ => s.lenUF Q)
      fun L old => arrLength op L old (.len (.arr op s P w) Q)
  | .copy s P src SQ, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (copyLeaf (src.lenUF SQ.elimF) (s.lenUF Q) (s.lenUF Q) (.len (.copy s P src SQ) Q)
        (fun pre => src.mapUF .map (SQ.elimF.addSegs pre))
        fun rest => src.lenUF (SQ.elimF.addSegs rest))
  | .view m i, Q => .len (.view m i) Q
termination_by structural s => s

/-- `LStor.mapU` as compiled code runs it. -/
def LStor.mapUF (sh : KShape) : LStor → LPath → LTerm
  | .init, Q => .kmap sh .init Q
  | .save s P _, Q => (cmpSegs P.elimF.segs Q.segs).toTerm (saveMap (s.mapUF sh Q))
  | .del s P, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (delMap (s.mapUF sh Q) P.elimF fun sh' q => s.mapUF sh' q)
  | .arr op s P w, Q =>
    let Pe := P.elimF
    (cmpSegs Pe.segs Q.segs).toTermLazy (fun _ => true) (fun _ => s.lenUF Pe)
      (fun _ => s.mapUF sh Q)
      fun L old => arrMap op L old (.kmap sh (.arr op s P w) Q)
  | .copy s P src SQ, Q => (cmpSegs P.elimF.segs Q.segs).toTerm
      (copyLeaf (src.mapUF sh SQ.elimF) (s.mapUF sh Q) (s.mapUF sh Q)
        (.kmap sh (.copy s P src SQ) Q)
        (fun pre => src.mapUF .map (SQ.elimF.addSegs pre))
        fun rest => src.mapUF sh (SQ.elimF.addSegs rest))
  | .view m i, Q => .kmap sh (.view m i) Q
termination_by structural s => s

end

/-- `arrRead` ignores the old length and value where it does not read them. -/
theorem arrRead_lazy (op : AOp) (w L old opq : LTerm) (slot : List SSeg → LTerm) (r : PathRel) :
    arrRead op w (if r.needsLen then L else .err) (if r.needsOld then old else .err) opq slot r =
      arrRead op w L old opq slot r := by
  cases r <;> rfl

/-- `arrHas` ignores what it does not read. -/
theorem arrHas_lazy (op : AOp) (L old opq : LTerm) (r : PathRel) :
    arrHas op (if r.needsLen then L else .err) (if r.needsOld then old else .err) opq r =
      arrHas op L old opq r := by
  cases r <;> rfl

/-- `arrLength` ignores what it does not read. -/
theorem arrLength_lazy (op : AOp) (L old opq : LTerm) (r : PathRel) :
    arrLength op (if r.needsLen then L else .err) (if r.needsOld then old else .err) opq r =
      arrLength op L old opq r := by
  cases r <;> rfl

/-- `arrMap` ignores the old length where it does not read it. -/
theorem arrMap_lazy (op : AOp) (L old opq : LTerm) (r : PathRel) :
    arrMap op (if r.needsLen then L else .err) (if true then old else .err) opq r =
      arrMap op L old opq r := by
  cases r <;> rfl

mutual

/-- The compiled elimination is the elimination. -/
theorem LTerm.elimF_eq : (t : LTerm) → t.elimF = t.elim
  | .lit _ | .var _ | .err | .env _ => rfl
  | .binop _ _ a b => by simp only [LTerm.elimF, LTerm.elim, LTerm.elimF_eq a, LTerm.elimF_eq b]
  | .unop _ _ a | .zero a => by simp only [LTerm.elimF, LTerm.elim, LTerm.elimF_eq a]
  | .ite c a b => by
    simp only [LTerm.elimF, LTerm.elim, LTerm.elimF_eq c, LTerm.elimF_eq a, LTerm.elimF_eq b]
  | .kite a b t e => by
    simp only [LTerm.elimF, LTerm.elim, LTerm.elimF_eq a, LTerm.elimF_eq b, LTerm.elimF_eq t,
      LTerm.elimF_eq e]
  | .seq a b | .orElse a b => by simp only [LTerm.elimF, LTerm.elim, LTerm.elimF_eq a,
      LTerm.elimF_eq b]
  | .find s q => by
    simp only [LTerm.elimF, LTerm.elim, LStor.okEF_eq s, LPath.elimF_eq q, LStor.readUF_eq s]
  | .has s q => by
    simp only [LTerm.elimF, LTerm.elim, LStor.okEF_eq s, LPath.elimF_eq q, LStor.hasUF_eq s]
  | .kmap sh s q => by
    simp only [LTerm.elimF, LTerm.elim, LStor.okEF_eq s, LPath.elimF_eq q, LStor.mapUF_eq sh s]
  | .len s q => by
    simp only [LTerm.elimF, LTerm.elim, LStor.okEF_eq s, LPath.elimF_eq q, LStor.lenUF_eq s]
  | .sok s => by simp only [LTerm.elimF, LTerm.elim, LStor.okEF_eq s]
  | .pok q => by simp only [LTerm.elimF, LTerm.elim, LPath.elimF_eq q]
  | .findP _ q => by simp only [LTerm.elimF, LTerm.elim, LPath.elimF_eq q]
  | .cpok _ _ => rfl
termination_by structural t => t

theorem LPath.elimF_eq : (q : LPath) → q.elimF = q.elim
  | .root _ => rfl
  | .field q _ => by simp only [LPath.elimF, LPath.elim, LPath.elimF_eq q]
  | .at q k => by simp only [LPath.elimF, LPath.elim, LPath.elimF_eq q, LTerm.elimF_eq k]
termination_by structural q => q

theorem LStor.okEF_eq : (s : LStor) → s.okEF = s.okE
  | .init => rfl
  | .save s q w => by
    simp only [LStor.okEF, LStor.okE, LStor.okEF_eq s, LTerm.elimF_eq w, LPath.elimF_eq q,
      LStor.hasUF_eq s]
  | .del s q => by
    simp only [LStor.okEF, LStor.okE, LStor.okEF_eq s, LPath.elimF_eq q, LStor.hasUF_eq s]
  | .arr _ s q w => by
    simp only [LStor.okEF, LStor.okE, LStor.okEF_eq s, LTerm.elimF_eq w, LPath.elimF_eq q,
      LStor.lenUF_eq s]
  | .copy s q src sq => by
    simp only [LStor.okEF, LStor.okE, LStor.okEF_eq s, LStor.okEF_eq src, LPath.elimF_eq q,
      LPath.elimF_eq sq, LStor.hasUF_eq s, LStor.hasUF_eq src]
  | .view _ _ => rfl
termination_by structural s => s

theorem LStor.readUF_eq : (s : LStor) → ∀ Q, s.readUF Q = s.readU Q
  | .init, _ => rfl
  | .save s P w, Q => by
    simp only [LStor.readUF, LStor.readU, LPath.elimF_eq P, LTerm.elimF_eq w, LStor.readUF_eq s]
  | .del s P, Q => by
    simp only [LStor.readUF, LStor.readU, LPath.elimF_eq P, LStor.readUF_eq s, LStor.mapUF_eq _ s]
  | .arr op s P w, Q => by
    simp only [LStor.readUF, LStor.readU, LPath.elimF_eq P, LTerm.elimF_eq w, LStor.readUF_eq s,
      LStor.lenUF_eq s, LStor.slotUF_eq s]
    exact CaseTree.toTermLazy_eq _ _ _ _ _ (arrRead_lazy op _ _ _ _ _)
  | .copy s P src SQ, Q => by
    simp only [LStor.readUF, LStor.readU, LPath.elimF_eq P, LPath.elimF_eq SQ, LStor.readUF_eq s,
      LStor.readUF_eq src, LStor.mapUF_eq _ src]
  | .view _ _, _ => rfl
termination_by structural s => s

theorem LStor.slotUF_eq : (s : LStor) → ∀ P rest opq, s.slotUF P rest opq = s.slotU P rest opq
  | .arr (.pop _) s P' _, P, rest, opq => by
    simp only [LStor.slotUF, LStor.slotU, LPath.elimF_eq P', LStor.readUF_eq s, LStor.lenUF_eq s,
      LStor.mapUF_eq _ s]
  | .del s P', P, rest, opq => by
    simp only [LStor.slotUF, LStor.slotU, LPath.elimF_eq P', LStor.readUF_eq s, LStor.lenUF_eq s,
      LStor.mapUF_eq _ s]
  | .init, _, _, _ | .save .., _, _, _ | .arr .push .., _, _, _
  | .arr (.slot _) .., _, _, _ | .copy .., _, _, _ | .view .., _, _, _ => rfl
termination_by structural s => s

theorem LStor.hasUF_eq : (s : LStor) → ∀ Q, s.hasUF Q = s.hasU Q
  | .init, _ => rfl
  | .save s P _, Q => by
    simp only [LStor.hasUF, LStor.hasU, LPath.elimF_eq P, LStor.hasUF_eq s]
  | .del s P, Q => by
    simp only [LStor.hasUF, LStor.hasU, LPath.elimF_eq P, LStor.hasUF_eq s, LStor.mapUF_eq _ s]
  | .arr op s P _, Q => by
    simp only [LStor.hasUF, LStor.hasU, LPath.elimF_eq P, LStor.hasUF_eq s, LStor.lenUF_eq s]
    exact CaseTree.toTermLazy_eq _ _ _ _ _ (arrHas_lazy op _ _ _)
  | .copy s P src SQ, Q => by
    simp only [LStor.hasUF, LStor.hasU, LPath.elimF_eq P, LPath.elimF_eq SQ, LStor.hasUF_eq s,
      LStor.hasUF_eq src, LStor.mapUF_eq _ src]
  | .view _ _, _ => rfl
termination_by structural s => s

theorem LStor.lenUF_eq : (s : LStor) → ∀ Q, s.lenUF Q = s.lenU Q
  | .init, _ => rfl
  | .save s P _, Q => by
    simp only [LStor.lenUF, LStor.lenU, LPath.elimF_eq P, LStor.lenUF_eq s]
  | .del s P, Q => by
    simp only [LStor.lenUF, LStor.lenU, LPath.elimF_eq P, LStor.lenUF_eq s, LStor.mapUF_eq _ s]
  | .arr op s P _, Q => by
    simp only [LStor.lenUF, LStor.lenU, LPath.elimF_eq P, LStor.lenUF_eq s]
    exact CaseTree.toTermLazy_eq _ _ _ _ _ (arrLength_lazy op _ _ _)
  | .copy s P src SQ, Q => by
    simp only [LStor.lenUF, LStor.lenU, LPath.elimF_eq P, LPath.elimF_eq SQ, LStor.lenUF_eq s,
      LStor.lenUF_eq src, LStor.mapUF_eq _ src]
  | .view _ _, _ => rfl
termination_by structural s => s

theorem LStor.mapUF_eq (sh : KShape) : (s : LStor) → ∀ Q, s.mapUF sh Q = s.mapU sh Q
  | .init, _ => rfl
  | .save s P _, Q => by
    simp only [LStor.mapUF, LStor.mapU, LPath.elimF_eq P, LStor.mapUF_eq sh s]
  | .del s P, Q => by
    simp only [LStor.mapUF, LStor.mapU, LPath.elimF_eq P, LStor.mapUF_eq _ s]
  | .arr op s P _, Q => by
    simp only [LStor.mapUF, LStor.mapU, LPath.elimF_eq P, LStor.mapUF_eq sh s, LStor.lenUF_eq s]
    exact CaseTree.toTermLazy_eq _ _ _ _ _ (arrMap_lazy op _ _ _)
  | .copy s P src SQ, Q => by
    simp only [LStor.mapUF, LStor.mapU, LPath.elimF_eq P, LPath.elimF_eq SQ, LStor.mapUF_eq sh s,
      LStor.mapUF_eq _ src]
  | .view _ _, _ => rfl
termination_by structural s => s

end

@[csimp] theorem LTerm.elim_csimp : @LTerm.elim = @LTerm.elimF :=
  funext fun t => (LTerm.elimF_eq t).symm

@[csimp] theorem LPath.elim_csimp : @LPath.elim = @LPath.elimF :=
  funext fun q => (LPath.elimF_eq q).symm

@[csimp] theorem LStor.okE_csimp : @LStor.okE = @LStor.okEF :=
  funext fun s => (LStor.okEF_eq s).symm

@[csimp] theorem LStor.readU_csimp : @LStor.readU = @LStor.readUF :=
  funext fun s => funext fun Q => (LStor.readUF_eq s Q).symm

@[csimp] theorem LStor.slotU_csimp : @LStor.slotU = @LStor.slotUF :=
  funext fun s => funext fun P => funext fun rest => funext fun opq =>
    (LStor.slotUF_eq s P rest opq).symm

@[csimp] theorem LStor.hasU_csimp : @LStor.hasU = @LStor.hasUF :=
  funext fun s => funext fun Q => (LStor.hasUF_eq s Q).symm

@[csimp] theorem LStor.lenU_csimp : @LStor.lenU = @LStor.lenUF :=
  funext fun s => funext fun Q => (LStor.lenUF_eq s Q).symm

@[csimp] theorem LStor.mapU_csimp : @LStor.mapU = @LStor.mapUF :=
  funext fun sh => funext fun s => funext fun Q => (LStor.mapUF_eq sh s Q).symm

/-- A formula with every read of a write eliminated. -/
def LFml.elim : LFml → LFml
  | .tt => .tt
  | .eq a b => .eq a.elim b.elim
  | .not φ => .not φ.elim
  | .and φ ψ => .and φ.elim ψ.elim
  | .imp φ ψ => .imp φ.elim ψ.elim
  | .all x p φ => .all x p φ.elim

/-! ### Eliminating keeps what returns -/


/-- A path without a `length` segment evaluates to one. -/
theorem LPath.noLen_eval (σ : State) : ∀ {q : LPath} {qs : List Seg},
    q.noLen = true → q.eval σ = .ok qs → NoLen qs
  | .root r, qs, hn, h => by
    cases h
    intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    simp only [LPath.noLen, bne_iff_ne, ne_eq] at hn
    intro he; exact hn (by injection he)
  | .field q f, qs, hn, h => by
    simp only [LPath.noLen, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
    obtain ⟨qs', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · exact LPath.noLen_eval σ hn.1 h' s hs
    · simp only [List.mem_singleton] at hs
      subst hs; intro he; exact hn.2 (by injection he)
  | .at q k, qs, hn, h => by
    simp only [LPath.noLen] at hn
    obtain ⟨qs', h', h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨i, _, he⟩ := Res.bind_eq_ok.1 h; cases he
    intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · exact LPath.noLen_eval σ hn h' s hs
    · simp only [List.mem_singleton] at hs
      subst hs; simp only [ne_eq, reduceCtorEq, not_false_eq_true]

/-- A read guarded by its storage and its path agrees with the read. -/
theorem guard_sim {σ : State} {s : LStor} {q q' : LPath} {X : LTerm} {F : SVal → List Seg → Res Value}
    (hs : Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true)))
    (hq : Sim (q'.eval σ) (q.eval σ))
    (hX : ∀ v qs, s.eval σ = .ok v → q'.eval σ = .ok qs → Sim (X.eval σ) (F v qs)) :
    Sim ((LTerm.seq s.okE (.seq (.pok q') X)).eval σ)
      (s.eval σ >>= fun v => q.eval σ >>= fun qs => F v qs) := by
  intro a
  simp only [LTerm.eval, Res.bind_eq_ok]
  constructor
  · rintro ⟨_, h₁, _, ⟨qs, h₂, -⟩, h₃⟩
    obtain ⟨v, hv, -⟩ := Res.bind_eq_ok.1 ((hs _).1 h₁)
    exact ⟨v, hv, qs, (hq _).1 h₂, (hX v qs hv h₂ a).1 h₃⟩
  · rintro ⟨v, hv, qs, hq', h₃⟩
    have h₂ := (hq qs).2 hq'
    exact ⟨.bool true, (hs _).2 (by simp only [hv, Res.ok_bind]), .bool true, ⟨qs, h₂, rfl⟩,
      (hX v qs hv h₂ a).2 h₃⟩

/-- A `delete` keeps the shape: the default of a mapping is a mapping, of a
fixed-size array a fixed-size array. -/
theorem KShape.test_defaultOf (sh : KShape) (c : SVal) : sh.test c.defaultOf = sh.test c := by
  cases c with
  | prim p => cases p <;> cases sh <;> rfl
  | struct _ => cases sh <;> rfl
  | array _ _ fx => cases fx <;> cases sh <;> rfl
  | map _ _ => cases sh <;> rfl

/-- A write below a location keeps its shape: after `ledger.balances[1] = 5;`,
`ledger.balances` is the mapping it was. -/
theorem save_cons_kmapF {sh : KShape} {v new u : SVal} {s : Seg} {r : List Seg}
    (h : v.saveLive (s :: r) new = .ok u) : sh.test u = sh.test v := by
  rcases saveLive_cons_shape h with ⟨_, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl, rfl, -⟩ | ⟨_, _, _, rfl, rfl⟩ <;>
    cases sh <;> rfl

/-- A write below an array keeps its length: after `values[2] = 5;`,
`values.length` is what it was. -/
theorem save_cons_arrLen {v new u : SVal} {s : Seg} {r : List Seg}
    (h : v.saveLive (s :: r) new = .ok u) : Close.arrLen u = Close.arrLen v := by
  rcases saveLive_cons_shape h with ⟨_, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl, rfl, hl⟩ | ⟨_, _, _, rfl, rfl⟩
  · rfl
  · simp only [Close.arrLen, hl]
  · rfl

/-- The members a list of segments starts with, up to its first key. -/
def leadFields : List SSeg → List Seg
  | .field f :: r => .field f :: leadFields r
  | _ => []

/-- Leading members have no key: `account.balance` of `account.balance[k]`. -/
theorem leadFields_noAt : (xs : List SSeg) → (leadFields xs).any Seg.isAt = false
  | .field _ :: r => by simp only [leadFields, List.any_cons, Seg.isAt, leadFields_noAt r,
      Bool.or_self]
  | [] => rfl
  | .key _ :: _ => rfl

/-- Segments with a key evaluate to their leading members, then a key. -/
theorem segsEval_leadFields (σ : State) : ∀ {xs : List SSeg} {ys : List Seg},
    segsEval σ xs = .ok ys → xs.any SSeg.isKey = true →
      ∃ k more, ys = leadFields xs ++ .at k :: more
  | [], _, _, hk => by simp only [List.any_nil, Bool.false_eq_true] at hk
  | .field f :: r, ys, h, hk => by
    obtain ⟨ys', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    obtain ⟨k, more, rfl⟩ := segsEval_leadFields σ h' (by simpa only [List.any_eq_true,
        SSeg.isKey, List.any_cons, Bool.false_or] using hk)
    exact ⟨k, more, rfl⟩
  | .key k :: r, ys, h, _ => by
    obtain ⟨i, _, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨ys', _, he⟩ := Res.bind_eq_ok.1 h; cases he
    exact ⟨i, ys', rfl⟩

/-- Extending a path by members appends them. -/
theorem LPath.addFields_eval (σ : State) : ∀ (xs : List SSeg) (q : LPath),
    (q.addFields xs).eval σ = q.eval σ >>= fun qs => .ok (qs ++ leadFields xs)
  | .field f :: r, q => by
    simp only [LPath.addFields, LPath.addFields_eval σ r, LPath.eval, bind_assoc, Res.ok_bind,
      leadFields, List.append_assoc, List.singleton_append]
  | [], q => by simp only [addFields, leadFields, List.append_nil, Close.bind_ok_right]
  | .key _ :: _, q => by simp only [addFields, leadFields, List.append_nil, Close.bind_ok_right]

/-- Agreeing runs, each with an agreeing fallback, agree. -/
theorem Sim.orElse {a a' b b' : Res Value} (ha : Sim a a') (hb : Sim b b') :
    Sim (orElseR a b) (orElseR a' b') := by
  intro x
  cases a with
  | ok v =>
    have h := (ha v).1 rfl
    rw [h]; rfl
  | error e =>
    cases a' with
    | ok v' => exact absurd ((ha v').2 rfl) (by simp only [reduceCtorEq, not_false_eq_true])
    | error _ => exact hb x

/-- A run that returns when a test does, and otherwise falls back. -/
theorem orElseR_eq_ok {a b : Res Value} {x : Value} :
    orElseR a b = .ok x ↔ a = .ok x ∨ ((∀ y, a ≠ .ok y) ∧ b = .ok x) := by
  cases a <;> simp only [orElseR, reduceCtorEq, ne_eq, not_false_eq_true, implies_true, true_and,
      false_or, Except.ok.injEq, forall_eq', false_and, or_false]

/-- The length of a default: a fixed-size array keeps its length, a dynamic
one has none left. -/
theorem lenEnd_sim {σ : State} {old fixed : LTerm} {x : Res SVal}
    (ho : Sim (old.eval σ) (x >>= Close.arrLen)) (hf : Sim (fixed.eval σ) (x >>= KShape.fixed.test)) :
    Sim ((lenEnd old fixed).eval σ) (x >>= fun w => Close.arrLen w.defaultOf) := by
  refine (Sim.orElse (Sim.bind hf fun _ => ho) (Sim.bind ho fun _ => Sim.refl _)).trans
    (Sim.of_eq ?_)
  rcases x with e | ⟨(i | b) | fs | ⟨es, sh, _ | _⟩ | ⟨es, d⟩⟩ <;>
    simp only [orElseR, bind, Except.bind, KShape.test, isFixV, Bool.false_eq_true, ↓reduceIte,
        Close.arrLen, SVal.defaultOf, LTerm.eval, defaultOfElems_eq_map, List.length_nil,
            Int.cast_ofNat_Int, List.length_map]

/-- **`delBelow` reads what the deleted value has below it.**  `v` is the
storage before the delete, `guard sh q` tests the location `q` names in it for
the shape `sh`, `atMap` is the old read of the whole path `full` and `atEnd`
its default; then the walk from `q` (at `qs`) down `rest` returns what the
default of the location at `qs` has at `rest`.  Example: `delete fixedMaps;`
then `fixedMaps[1][2]`: `fixedMaps` is a fixed-size array (its element `1` is
deleted in place), `fixedMaps[1]` a mapping (its entry `2` is the old one). -/
theorem delBelow_sim {σ : State} {v : SVal} {G : SVal → Res Value} {atMap atEnd : LTerm}
    {guard : KShape → LPath → LTerm} {full : List Seg}
    (hg : ∀ sh q qs, q.eval σ = .ok qs → Sim ((guard sh q).eval σ) (v.findLive qs >>= sh.test))
    (hMap : Sim (atMap.eval σ) (v.findLive full >>= G))
    (hEnd : Sim (atEnd.eval σ) (v.findLive full >>= fun w => G w.defaultOf)) :
    ∀ (rest : List SSeg) (q : LPath) (qs R : List Seg), q.eval σ = .ok qs →
      segsEval σ rest = .ok R → qs ++ R = full →
      Sim ((delBelow atMap atEnd guard q rest).eval σ)
        (v.findLive qs >>= fun N => N.defaultOf.findLive R >>= G)
  | [], q, qs, R, hq, hR, hf => by
    cases hR
    simp only [delBelow, List.append_nil] at hf ⊢
    subst hf
    refine hEnd.trans (Sim.of_eq ?_)
    congr 1; funext N
    simp only [SVal.findLive_nil, Res.ok_bind]
  | .field f :: r, q, qs, R, hq, hR, hf => by
    obtain ⟨R', hR', he⟩ := Res.bind_eq_ok.1 hR; cases he
    have hq' : (q.field f).eval σ = .ok (qs ++ [.field f]) := by
      simp only [LPath.eval, hq, Res.ok_bind]
    have ih := delBelow_sim hg hMap hEnd r (q.field f) (qs ++ [.field f]) R' hq' hR'
      (by rw [← hf]; simp only [List.append_assoc, List.cons_append, List.nil_append])
    simp only [delBelow]
    refine ih.trans (Sim.of_eq ?_)
    rw [SVal.findLive_append, bind_assoc]
    congr 1; funext N
    rw [defaultOf_field, bind_assoc]
  | .key k :: r, q, qs, R, hq, hR, hf => by
    obtain ⟨i, hi, hR⟩ := Res.bind_eq_ok.1 hR
    obtain ⟨R', hR', he⟩ := Res.bind_eq_ok.1 hR; cases he
    have hq' : (q.at k).eval σ = .ok (qs ++ [.at i]) := by
      simp only [LPath.eval, hq, Res.ok_bind, hi]
    have ih := delBelow_sim hg hMap hEnd r (q.at k) (qs ++ [.at i]) R' hq' hR'
      (by rw [← hf]; simp only [List.append_assoc, List.cons_append, List.nil_append])
    have hgm := hg .map q qs hq
    have hgf := hg .fixed q qs hq
    simp only [delBelow]
    intro a
    simp only [LTerm.eval, orElseR_eq_ok, Res.bind_eq_ok]
    constructor
    · rintro (⟨x, h₁, h₂⟩ | ⟨hA, x, h₁, h₂⟩)
      · -- a mapping: the old read
        obtain ⟨N, hN, hm⟩ := Res.bind_eq_ok.1 ((hgm x).1 h₁)
        have hmap : isMapV N = true := by
          simp only [KShape.test, kmapF] at hm; split at hm
          · assumption
          · simp only [reduceCtorEq] at hm
        obtain ⟨N', hN', hr⟩ := Res.bind_eq_ok.1 (by
          have := (hMap a).1 h₂; rw [← hf, SVal.findLive_append] at this; rw [bind_assoc] at this
          exact this)
        rw [hN] at hN'; cases hN'
        obtain ⟨b, hb, hG⟩ := Res.bind_eq_ok.1 hr
        exact ⟨N, hN, b, (defaultOf_key N i R' b).2 (.inl ⟨hmap, hb⟩), hG⟩
      · -- a fixed-size array: the element, one key down
        obtain ⟨N, hN, hx⟩ := Res.bind_eq_ok.1 ((hgf x).1 h₁)
        have hfix : isFixV N = true := by
          simp only [KShape.test] at hx; split at hx
          · assumption
          · simp only [reduceCtorEq] at hx
        obtain ⟨e, he, hr⟩ := Res.bind_eq_ok.1 (by
          have := (ih a).1 h₂; rw [SVal.findLive_append, bind_assoc, hN, Res.ok_bind] at this
          exact this)
        obtain ⟨b, hb, hG⟩ := Res.bind_eq_ok.1 hr
        exact ⟨N, hN, b, (defaultOf_key N i R' b).2 (.inr ⟨hfix, e, he, hb⟩), hG⟩
    · rintro ⟨N, hN, b, hb, hG⟩
      rcases (defaultOf_key N i R' b).1 hb with ⟨hmap, hb'⟩ | ⟨hfix, e, he, hb'⟩
      · refine .inl ⟨.bool true, (hgm _).2 ?_, (hMap a).2 ?_⟩
        · simp only [hN, Res.ok_bind, KShape.test, kmapF, hmap, ↓reduceIte]
        · rw [← hf, SVal.findLive_append, bind_assoc, hN, Res.ok_bind, hb', Res.ok_bind, hG]
      · have hnm : isMapV N = false := by
          cases N <;> simp_all only [isFixV, Bool.false_eq_true, isMapV]
        refine .inr ⟨fun y hy => ?_, .bool true, (hgf _).2 ?_, (ih a).2 ?_⟩
        · obtain ⟨z, hz, _⟩ := Res.bind_eq_ok.1 hy
          obtain ⟨N', hN', hm⟩ := Res.bind_eq_ok.1 ((hgm z).1 hz)
          rw [hN] at hN'; cases hN'
          simp only [KShape.test, kmapF, hnm, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hm
        · simp only [hN, Res.ok_bind, KShape.test, hfix, ↓reduceIte]
        · rw [SVal.findLive_append, bind_assoc, hN, Res.ok_bind, he, Res.ok_bind, hb',
            Res.ok_bind, hG]

/-- A word has nothing below it. -/
theorem find_prim_cons (p : PrimVal) (f : Seg) (t : List Seg) :
    (SVal.prim p).findLive (f :: t) = .error .stuck := by
  cases f <;> rfl

/-- The case tree comparing a write at `P` with a read at `Q` agrees with a
run when every leaf whose relation holds of the two paths does. -/
theorem cmp_sim {σ : State} {P Q : LPath} {ps qs : List Seg} (hp : P.eval σ = .ok ps)
    (hq : Q.eval σ = .ok qs) {leaf : PathRel → LTerm} {y : Res Value}
    (h : ∀ r : PathRel, r.Holds σ ps qs → Sim ((leaf r).eval σ) y) :
    Sim (((cmpSegs P.segs Q.segs).toTerm leaf).eval σ) y := by
  have hp' := LPath.segs_eval σ hp
  have hq' := LPath.segs_eval σ hq
  rw [CaseTree.toTerm_eval σ _ _ (cmpSegs_testsOk σ _ _ hp' hq')]
  exact h _ (cmpSegs_holds σ _ _ hp' hq')

theorem LPath.addSegs_eval (σ : State) : ∀ (xs : List SSeg) (q : LPath),
    (q.addSegs xs).eval σ = q.eval σ >>= fun qs => segsEval σ xs >>= fun r => .ok (qs ++ r)
  | [], q => by
    simp only [LPath.addSegs, segsEval, Res.ok_bind, List.append_nil]
    cases q.eval σ <;> rfl
  | .field f :: xs, q => by
    rw [LPath.addSegs, LPath.addSegs_eval σ xs]
    simp only [LPath.eval, segsEval, bind_assoc, Res.ok_bind, List.append_assoc,
      List.singleton_append]
  | .key k :: xs, q => by
    rw [LPath.addSegs, LPath.addSegs_eval σ xs]
    simp only [LPath.eval, segsEval, bind_assoc, Res.ok_bind, List.append_assoc,
      List.singleton_append]

theorem isT_eval (σ : State) (t : LTerm) :
    (isT t).eval σ = .ok (.bool (match t.eval σ with | .ok _ => true | .error _ => false)) := by
  unfold isT
  simp only [LTerm.eval]
  cases t.eval σ <;> rfl

/-! ### Arrays and copies

An operation on an array changes the node at its path alone (`AOp.apply`):
below it a read compares its index with the old length (`arrKey`); a copy
reads the source through members (`overlay_findLive_fields`), and below a
key of a copy the read is kept whole, since a mapping met in both keeps the
target's entries. -/

theorem findLive_grow (es sh sh' : List SVal) (fx : Bool) (x : SVal) (i : Int) (r : List Seg) :
    (SVal.array (es ++ [x]) sh' fx).findLive (.at i :: r) =
      if i = es.length then x.findLive r else (SVal.array es sh fx).findLive (.at i :: r) := by
  simp only [SVal.findLive, List.length_append, List.length_singleton, List.get_eq_getElem]
  by_cases hi : i = es.length
  · subst hi
    simp only [Int.ofNat_zero_le, Int.toNat_natCast, Nat.lt_add_one, and_self, ↓reduceDIte,
        Nat.le_refl, List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero, ↓reduceIte]
  · rw [if_neg hi]
    by_cases hb : 0 ≤ i ∧ i.toNat < es.length
    · rw [dif_pos hb, dif_pos (by omega)]
      rw [List.getElem_append_left]
    · rw [dif_neg hb, dif_neg (by omega)]

theorem findLive_shrink (es sh sh' : List SVal) (fx : Bool) (x : SVal) (i : Int) (r : List Seg) :
    (SVal.array es sh' fx).findLive (.at i :: r) =
      if i = es.length then .error .revert else (SVal.array (es ++ [x]) sh fx).findLive (.at i :: r) := by
  rw [findLive_grow es sh' sh fx x i r]
  by_cases hi : i = es.length
  · subst hi
    simp only [SVal.findLive, Int.ofNat_zero_le, Int.toNat_natCast, Nat.lt_irrefl, and_false,
        ↓reduceDIte, ↓reduceIte]
  · simp only [hi, ↓reduceIte]

theorem layAt_overlay : ∀ (old : SVal) (q : List Seg) (v : SVal), ∃ c : SVal, Close.layAt old q v = c.overlay v
  | old, [], v => ⟨old, by cases old <;> simp only [Close.layAt]⟩
  | .struct ofs, .field f :: q, v => by
    simp only [Close.layAt]
    split
    · exact layAt_overlay _ q v
    · exact ⟨.prim (.int 0), (prim_overlay _ v).symm⟩
  | .prim _, _ :: _, v | .array .., _ :: _, v | .map .., _ :: _, v | .struct _, .at _ :: _, v =>
    ⟨.prim (.int 0), (prim_overlay _ v).symm⟩

theorem overlayElems_length : ∀ (os nel : List SVal), (SVal.overlay.overlayElems os nel).length = nel.length
  | o :: os, _ :: nel => by simp only [SVal.overlay.overlayElems, List.length_cons,
      overlayElems_length os nel]
  | [], nel => by simp only [SVal.overlay.overlayElems, Close.stripElems_length]
  | _ :: _, [] => rfl

theorem overlay_asValue (c y : SVal) : (c.overlay y).asValue = y.asValue := by
  cases y with
  | prim p => cases c <;> simp only [SVal.overlay, SVal.strip]
  | struct _ => cases c <;> simp only [SVal.asValue, SVal.overlay, SVal.strip]
  | array _ _ _ => cases c <;> simp only [SVal.asValue, SVal.overlay, SVal.strip]
  | map _ _ => cases c <;> simp only [SVal.asValue, SVal.overlay, SVal.strip]

theorem overlay_arrLen (c y : SVal) : Close.arrLen (c.overlay y) = Close.arrLen y := by
  cases y with
  | array nel nsh nfx =>
    cases c <;> simp only [Close.arrLen, SVal.overlay, SVal.strip, Close.stripElems_length,
        overlayElems_length]
  | prim p => cases c <;> simp only [SVal.overlay, SVal.strip]
  | struct _ => cases c <;> simp only [Close.arrLen, SVal.overlay, SVal.strip]
  | map _ _ => cases c <;> simp only [Close.arrLen, SVal.overlay, SVal.strip]


theorem overlay_test (sh : KShape) (c y : SVal) : sh.test (c.overlay y) = sh.test y := by
  cases y with
  | array nel nsh nfx =>
    cases c <;> cases sh <;> simp only [KShape.test, kmapF, isMapV, SVal.overlay, SVal.strip,
        Bool.false_eq_true, ↓reduceIte, isFixV]
  | prim p => cases c <;> simp only [SVal.overlay, SVal.strip]
  | struct _ => cases c <;> cases sh <;> simp only [KShape.test, kmapF, isMapV, SVal.overlay,
      SVal.strip, Bool.false_eq_true, ↓reduceIte, isFixV]
  | map _ _ => cases c <;> cases sh <;> simp only [KShape.test, kmapF, isMapV, SVal.overlay,
      SVal.strip, ↓reduceIte, isFixV, Bool.false_eq_true]

theorem fieldPath_of_any : ∀ (fs : List Seg), fs.any Seg.isAt = false → Close.fieldPath fs = true
  | [], _ => rfl
  | .field _ :: fs, h => by
    simpa only [Close.fieldPath_field] using fieldPath_of_any fs (by
      simpa only [List.any_eq_false, Seg.isAt, Bool.not_eq_true, List.any_cons, Bool.false_or]
        using h)
  | .at _ :: _, h => by simp only [List.any_cons, Seg.isAt, Bool.true_or, Bool.true_eq_false] at h

/-- **A copy read along members reads the source**, up to what a read of a
word, a location, a length or a shape sees (`hG`). -/
theorem overlay_findLive_fields {G : SVal → Res Value} (hG : ∀ c y : SVal, G (c.overlay y) = G y)
    (cur n : SVal) (fs : List Seg) (hf : fs.any Seg.isAt = false) :
    ((cur.overlay n).findLive fs >>= G) = (n.findLive fs >>= G) := by
  rw [findLive_eq_find _ _ hf, findLive_eq_find _ _ hf,
    Close.find_overlay_fields cur n fs (fieldPath_of_any fs hf)]
  cases n.find fs with
  | error _ => rfl
  | ok v =>
    obtain ⟨c, hc⟩ := layAt_overlay cur fs v
    simp only [Res.ok_bind, hc, hG]

theorem AOp.apply_pop {keep : Bool} {wv : Value} {c c' : SVal}
    (h : (AOp.pop keep).apply wv c = .ok c') :
    ∃ es last sh fx sh', c = .array (es ++ [last]) sh fx ∧ c' = .array es sh' fx := by
  cases c with
  | array elems shadow fx =>
    simp only [AOp.apply] at h
    rcases hr : elems.reverse with _ | ⟨l, rr⟩ <;> simp only [hr] at h
    · cases h
    · cases h
      refine ⟨rr.reverse, l, shadow, fx, _, ?_, rfl⟩
      have he : elems = (l :: rr).reverse := by rw [← hr, List.reverse_reverse]
      simp only [he, List.reverse_cons]
  | prim _ | struct _ | map _ _ => simp only [apply, reduceCtorEq] at h

/-- The array an operation leaves, against the one it found. -/
theorem AOp.apply_ok {op : AOp} {wv : Value} {c c' : SVal} (h : op.apply wv c = .ok c') :
    ∃ es sh fx es' sh', c = .array es sh fx ∧ c' = .array es' sh' fx ∧
      (es'.length : Int) = (match op with | .pop _ => (es.length : Int) - 1 | _ => es.length + 1) := by
  cases op with
  | push =>
    cases c with
    | array es sh fx => simp only [AOp.apply] at h; cases h; exact ⟨es, sh, fx, _, _, rfl, rfl,
        by simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
            Int.natCast_add, Int.cast_ofNat_Int]⟩
    | prim _ | struct _ | map _ _ => simp only [apply, reduceCtorEq] at h
  | slot E =>
    cases c with
    | array es sh fx => simp only [AOp.apply] at h; cases h; exact ⟨es, sh, fx, _, _, rfl, rfl,
        by simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
            Int.natCast_add, Int.cast_ofNat_Int]⟩
    | prim _ | struct _ | map _ _ => simp only [apply, reduceCtorEq] at h
  | pop keep =>
    obtain ⟨es, last, sh, fx, sh', rfl, rfl⟩ := AOp.apply_pop h
    exact ⟨_, sh, fx, es, sh', rfl, rfl, by simp only [List.length_append, List.length_cons,
        List.length_nil, Nat.zero_add, Int.natCast_add, Int.cast_ofNat_Int, Int.add_sub_cancel]⟩

theorem pushSlot_prim (p : PrimTy) (sh : List SVal) :
    (pushSlot (.prim p) sh).1 = .prim (dfltV p) := by
  cases sh <;> cases p <;> simp only [pushSlot, defaultForTy, dfltV, Ty.isPrimitive,
      ↓reduceIte] <;> rfl

theorem kite_eval {σ : State} {k L t e : LTerm} {i n : Int}
    (hk : (k.eval σ >>= Value.asInt) = .ok i) (hL : L.eval σ = .ok (.int n)) :
    (LTerm.kite k L t e).eval σ = if i = n then t.eval σ else e.eval σ := by
  simp only [LTerm.eval, hk, hL, Res.ok_bind, Value.asInt]

theorem lenPred_eval {σ : State} {L : LTerm} {n : Int} (h : L.eval σ = .ok (.int n)) :
    (lenPred L).eval σ = .ok (.int (n - 1)) := by
  simp only [lenPred, LTerm.eval, bind, Except.bind, h, evalBinop, applyBinOp, Value.asInt,
      checkArith, BinOp.retTy, BinOp.isArith, ↓reduceIte]

theorem lenSucc_eval {σ : State} {L : LTerm} {n : Int} (h : L.eval σ = .ok (.int n)) :
    (lenSucc L).eval σ = .ok (.int (n + 1)) := by
  simp only [lenSucc, LTerm.eval, bind, Except.bind, h, evalBinop, applyBinOp, Value.asInt,
      checkArith, BinOp.retTy, BinOp.isArith, ↓reduceIte]

/-- **What is at an index after an operation on the array.** -/
theorem arrKey_sim {σ : State} {op : AOp} {wv : Value} {c c' : SVal} {k L old opq atNew : LTerm}
    {i : Int} {r : List Seg} {G : SVal → Res Value}
    (hap : op.apply wv c = .ok c') (hk : (k.eval σ >>= Value.asInt) = .ok i)
    (hL : Sim (L.eval σ) (Close.arrLen c))
    (hold : Sim (old.eval σ) (c.findLive (.at i :: r) >>= G))
    (hopq : Sim (opq.eval σ) (c'.findLive (.at i :: r) >>= G))
    (hnew : ∀ pv : PrimVal, (op = .push → SVal.prim pv = wv.toSVal) →
      (∀ p, op = .slot (.prim p) → SVal.prim pv = .prim (dfltV p)) →
      (op = .push ∨ ∃ p, op = .slot (.prim p)) → Sim (atNew.eval σ) ((SVal.prim pv).findLive r >>= G)) :
    Sim ((arrKey op L k old opq atNew).eval σ) (c'.findLive (.at i :: r) >>= G) := by
  cases op with
  | push =>
    cases c with
    | array es sh fx =>
      simp only [AOp.apply] at hap; cases hap
      have hL' : L.eval σ = .ok (.int es.length) := (hL _).2 rfl
      simp only [arrKey, kite_eval hk hL', findLive_grow es sh _ fx _ i r]
      split
      · cases wv with
        | int n => exact hnew (.int n) (fun _ => rfl) (fun _ h => by cases h) (.inl rfl)
        | bool b => exact hnew (.bool b) (fun _ => rfl) (fun _ h => by cases h) (.inl rfl)
      · exact hold
    | prim _ | struct _ | map _ _ => simp only [AOp.apply, reduceCtorEq] at hap
  | slot E =>
    cases c with
    | array es sh fx =>
      simp only [AOp.apply] at hap; cases hap
      have hL' : L.eval σ = .ok (.int es.length) := (hL _).2 rfl
      cases E with
      | prim p =>
        simp only [arrKey, kite_eval hk hL', findLive_grow es sh _ fx _ i r, pushSlot_prim]
        split
        · exact hnew (dfltV p) (fun h => by cases h) (fun _ h => by cases h; rfl) (.inr ⟨p, rfl⟩)
        · exact hold
      | ref R =>
        simp only [arrKey]
        exact hopq
    | prim _ | struct _ | map _ _ => simp only [AOp.apply, reduceCtorEq] at hap
  | pop keep =>
    obtain ⟨es, last, sh, fx, sh', rfl, rfl⟩ := AOp.apply_pop hap
    have hL' : L.eval σ = .ok (.int (es ++ [last]).length) := (hL _).2 rfl
    have hP : (lenPred L).eval σ = .ok (.int es.length) := by
      rw [lenPred_eval hL']; simp only [List.length_append, List.length_cons, List.length_nil,
          Nat.zero_add, Int.natCast_add, Int.cast_ofNat_Int, Int.add_sub_cancel]
    simp only [arrKey, kite_eval hk hP, findLive_shrink es sh sh' fx last i r]
    split
    · exact Sim.halt (by simp only [LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
        implies_true]) (by simp only [Res.error_bind, ne_eq, reduceCtorEq, not_false_eq_true,
            implies_true])
    · exact hold

theorem below_cases {σ : State} {rest : List SSeg} {f : Seg} {r : List Seg}
    (h : segsEval σ rest = .ok (f :: r)) :
    (∃ g rest', rest = .field g :: rest') ∨
      ∃ k rest' i, rest = .key k :: rest' ∧ (k.eval σ >>= Value.asInt) = .ok i ∧ f = .at i ∧
        segsEval σ rest' = .ok r := by
  cases rest with
  | nil => simp only [segsEval, Except.ok.injEq, List.nil_eq, reduceCtorEq] at h
  | cons x rest' =>
    cases x with
    | field g => exact .inl ⟨g, rest', rfl⟩
    | key k =>
      obtain ⟨i, hi, h⟩ := Res.bind_eq_ok.1 h
      obtain ⟨r', hr', he⟩ := Res.bind_eq_ok.1 h
      cases he
      exact .inr ⟨k, rest', i, rfl, hi, rfl, hr'⟩

theorem segsEval_isEmpty {σ : State} : ∀ {xs : List SSeg} {ys : List Seg},
    segsEval σ xs = .ok ys → (xs.isEmpty = true ↔ ys = [])
  | [], ys, h => by cases h; simp only [List.isEmpty_nil]
  | .field f :: xs, ys, h => by
    obtain ⟨_, _, he⟩ := Res.bind_eq_ok.1 h; cases he; simp only [List.isEmpty_cons,
        Bool.false_eq_true, reduceCtorEq]
  | .key k :: xs, ys, h => by
    obtain ⟨_, _, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨_, _, he⟩ := Res.bind_eq_ok.1 h; cases he; simp only [List.isEmpty_cons,
        Bool.false_eq_true, reduceCtorEq]

theorem segsEval_lead {σ : State} : ∀ {xs : List SSeg} {ys : List Seg},
    segsEval σ xs = .ok ys → xs.any SSeg.isKey = false → ys = leadFields xs
  | [], ys, h, _ => by cases h; rfl
  | .field f :: xs, ys, h, hk => by
    obtain ⟨ys', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    simp only [segsEval_lead h' (by simpa only [List.any_eq_false, SSeg.isKey, Bool.not_eq_true,
        List.any_cons, Bool.false_or] using hk), leadFields]
  | .key _ :: _, _, _, hk => by simp only [List.any_cons, SSeg.isKey, Bool.true_or,
      Bool.true_eq_false] at hk

/-- Below a word: what a read finds at its end, nothing past it. -/
theorem prim_leaf_sim {σ : State} {pv : PrimVal} {t : List Seg} {rest : List SSeg}
    {G : SVal → Res Value} {a : LTerm} (hemp : rest.isEmpty = true ↔ t = [])
    (ha : Sim (a.eval σ) (G (.prim pv))) :
    Sim ((if rest.isEmpty then a else .err).eval σ) ((SVal.prim pv).findLive t >>= G) := by
  by_cases ht : t = []
  · subst ht
    rw [if_pos (hemp.2 rfl)]
    simpa only [SVal.findLive] using ha
  · rw [if_neg (fun h => ht (hemp.1 h))]
    obtain ⟨f, t', rfl⟩ := List.exists_cons_of_ne_nil ht
    exact Sim.halt (by simp only [LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
        implies_true]) (by simp only [find_prim_cons, Res.error_bind, ne_eq, reduceCtorEq,
            not_false_eq_true, implies_true])

/-- Below a word, where only a location would do. -/
theorem prim_err_sim {σ : State} {pv : PrimVal} {t : List Seg} {G : SVal → Res Value}
    (hG : ∀ p x, G (.prim p) ≠ .ok x) :
    Sim (LTerm.err.eval σ) ((SVal.prim pv).findLive t >>= G) := by
  refine Sim.halt (by simp only [LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
      implies_true]) fun x hx => ?_
  cases t with
  | nil => exact hG pv x (by simpa only [SVal.findLive] using hx)
  | cons f t' => simp only [find_prim_cons, Res.error_bind, reduceCtorEq] at hx

theorem arrRead_sim {σ : State} {op : AOp} {wv : Value} {w L old opq : LTerm}
    {slot : List SSeg → LTerm} {v c c' u : SVal} {ps qs : List Seg}
    (hc : v.findLive ps = .ok c) (hap : op.apply wv c = .ok c') (hu : v.saveLive ps c' = .ok u)
    (hw : w.eval σ = .ok wv) (hL : Sim (L.eval σ) (Close.arrLen c))
    (hold : Sim (old.eval σ) (v.findLive qs >>= SVal.asValue))
    (hopq : Sim (opq.eval σ) (u.findLive qs >>= SVal.asValue))
    (hslot : ∀ es sh fx R, c = .array es sh fx → op = .slot (.ref R) → ∀ rest r,
      segsEval σ rest = .ok r →
      Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) →
      Sim ((slot rest).eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue))
    (r : PathRel) (hr : r.Holds σ ps qs) :
    Sim ((arrRead op w L old opq slot r).eval σ) (u.findLive qs >>= SVal.asValue) := by
  cases r with
  | eq =>
    simp only [PathRel.Holds] at hr; subst hr
    obtain ⟨es, sh, fx, es', sh', -, rfl, -⟩ := AOp.apply_ok hap
    refine Sim.halt (by simp only [arrRead, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
        implies_true]) ?_
    simp only [findLive_saveLive_same hu, Res.ok_bind, SVal.asValue, ne_eq, reduceCtorEq,
        not_false_eq_true, implies_true]
  | above =>
    obtain ⟨f, t, rfl⟩ := hr
    obtain ⟨_, w', _, hs', hf⟩ := save_through qs (f :: t) hu
    obtain ⟨e, he⟩ := save_cons_asValue hs'
    refine Sim.halt (by simp only [arrRead, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
        implies_true]) ?_
    simp only [hf, Res.ok_bind, he, ne_eq, reduceCtorEq, not_false_eq_true, implies_true]
  | diverge => rw [findLive_saveLive_diverge hr hu]; exact hold
  | below rest =>
    obtain ⟨f, t, rfl, hrest⟩ := hr
    rcases below_cases hrest with ⟨g, rest', rfl⟩ | ⟨k, rest', i, rfl, hk, rfl, hr'⟩
    · exact hopq
    · simp only [arrRead]
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind] at hopq ⊢
      rw [SVal.findLive_append, hc, Res.ok_bind] at hold
      by_cases hop : ∃ R, op = .slot (.ref R)
      · obtain ⟨R, rfl⟩ := hop
        cases c with
        | array es sh fx =>
          simp only [AOp.apply] at hap; cases hap
          have hL' : L.eval σ = .ok (.int es.length) := (hL _).2 rfl
          simp only [kite_eval hk hL']
          rw [findLive_grow es sh _ fx _ i t] at hopq ⊢
          by_cases hi : i = es.length
          · rw [if_pos hi] at hopq
            rw [if_pos hi, if_pos hi]
            exact hslot es sh fx R rfl rfl rest' t hr' hopq
          · rw [if_neg hi, if_neg hi]
            exact hold
        | prim _ | struct _ | map _ _ => simp only [AOp.apply, reduceCtorEq] at hap
      · split
        · rename_i R; exact absurd ⟨R, rfl⟩ hop
        refine arrKey_sim hap hk hL hold hopq fun pv h1 h2 h3 => ?_
        have hemp := segsEval_isEmpty hr'
        rcases h3 with rfl | ⟨p, rfl⟩
        · refine prim_leaf_sim hemp (Sim.of_eq ?_)
          rw [h1 rfl, Close.asValue_toSVal, hw]
        · refine prim_leaf_sim hemp (Sim.of_eq ?_)
          rw [h2 p rfl]
          cases p <;> rfl

theorem arrHas_sim {σ : State} {op : AOp} {wv : Value} {L old opq : LTerm} {v c c' u : SVal}
    {ps qs : List Seg}
    (hc : v.findLive ps = .ok c) (hap : op.apply wv c = .ok c') (hu : v.saveLive ps c' = .ok u)
    (hL : Sim (L.eval σ) (Close.arrLen c))
    (hold : Sim (old.eval σ) (v.findLive qs >>= fun _ => .ok (.bool true)))
    (hopq : Sim (opq.eval σ) (u.findLive qs >>= fun _ => .ok (.bool true)))
    (r : PathRel) (hr : r.Holds σ ps qs) :
    Sim ((arrHas op L old opq r).eval σ) (u.findLive qs >>= fun _ => .ok (.bool true)) := by
  cases r with
  | eq =>
    simp only [PathRel.Holds] at hr; subst hr
    exact Sim.of_eq (by simp only [arrHas, LTerm.eval, findLive_saveLive_same hu, Res.ok_bind])
  | above =>
    obtain ⟨f, t, rfl⟩ := hr
    obtain ⟨_, w', _, _, hf⟩ := save_through qs (f :: t) hu
    exact Sim.of_eq (by simp only [arrHas, LTerm.eval, hf, Res.ok_bind])
  | diverge => rw [findLive_saveLive_diverge hr hu]; exact hold
  | below rest =>
    obtain ⟨f, t, rfl, hrest⟩ := hr
    rcases below_cases hrest with ⟨g, rest', rfl⟩ | ⟨k, rest', i, rfl, hk, rfl, hr'⟩
    · exact hopq
    · simp only [arrHas]
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind] at hopq ⊢
      rw [SVal.findLive_append, hc, Res.ok_bind] at hold
      by_cases hop : ∃ R, op = .slot (.ref R)
      · obtain ⟨R, rfl⟩ := hop
        simp only
        split
        · rename_i hemp
          have ht : t = [] := (segsEval_isEmpty hr').1 hemp
          subst ht
          cases c with
          | array es sh fx =>
            simp only [AOp.apply] at hap; cases hap
            have hL' : L.eval σ = .ok (.int es.length) := (hL _).2 rfl
            obtain ⟨x, hx, hxi⟩ := Res.bind_eq_ok.1 hk
            cases x with
            | bool b => simp only [Value.asInt, reduceCtorEq] at hxi
            | int j =>
              simp only [Value.asInt, Except.ok.injEq] at hxi
              subst hxi
              have hT : (inRange k L).eval σ =
                  (if 0 ≤ j ∧ j ≤ es.length then (.ok (.bool true) : Res Value) else .error .stuck) := by
                simp only [inRange, LTerm.eval, hx, hL', evalBinop, applyBinOp, Value.asInt,
                  Value.asBool, checkArith, pickBranch, bind, Except.bind, pure, Except.pure]
                by_cases h0 : 0 ≤ j <;> by_cases h1 : j ≤ (es.length : Int) <;>
                  simp only [h0, decide_true, h1, Bool.and_self, and_self, ↓reduceIte,
                      decide_false, Bool.and_false, and_false, and_true]
              have hR : ((SVal.array (es ++ [(pushSlot (Ty.ref R) sh).1]) (pushSlot (Ty.ref R) sh).2
                  fx).findLive [.at j] >>= fun _ => .ok (.bool true)) =
                  (if 0 ≤ j ∧ j ≤ es.length then (.ok (.bool true) : Res Value) else .error .revert) := by
                simp only [SVal.findLive, List.length_append, List.length_singleton]
                by_cases hj : 0 ≤ j ∧ j ≤ es.length
                · have hj' : 0 ≤ j ∧ j.toNat < es.length + 1 := ⟨hj.1, by omega⟩
                  simp only [hj', and_self, ↓reduceDIte, List.get_eq_getElem, Res.ok_bind, hj,
                      ↓reduceIte]
                · have hj' : ¬(0 ≤ j ∧ j.toNat < es.length + 1) := by omega
                  rw [dif_neg hj', if_neg hj]; rfl
              rw [hT, hR]
              split
              · exact Sim.refl _
              · exact Sim.halt (by simp only [ne_eq, reduceCtorEq, not_false_eq_true,
                  implies_true]) (by simp only [ne_eq, reduceCtorEq, not_false_eq_true,
                      implies_true])
          | prim _ | struct _ | map _ _ => simp only [AOp.apply, reduceCtorEq] at hap
        · exact hopq
      · split
        · rename_i R; exact absurd ⟨R, rfl⟩ hop
        exact arrKey_sim hap hk hL hold hopq fun pv _ _ _ =>
          prim_leaf_sim (segsEval_isEmpty hr') (Sim.of_eq rfl)

theorem arrLength_sim {σ : State} {op : AOp} {wv : Value} {L old opq : LTerm} {v c c' u : SVal}
    {ps qs : List Seg}
    (hc : v.findLive ps = .ok c) (hap : op.apply wv c = .ok c') (hu : v.saveLive ps c' = .ok u)
    (hL : Sim (L.eval σ) (Close.arrLen c))
    (hold : Sim (old.eval σ) (v.findLive qs >>= Close.arrLen))
    (hopq : Sim (opq.eval σ) (u.findLive qs >>= Close.arrLen))
    (r : PathRel) (hr : r.Holds σ ps qs) :
    Sim ((arrLength op L old opq r).eval σ) (u.findLive qs >>= Close.arrLen) := by
  cases r with
  | eq =>
    simp only [PathRel.Holds] at hr; subst hr
    obtain ⟨es, sh, fx, es', sh', rfl, rfl, hlen⟩ := AOp.apply_ok hap
    have hL' : L.eval σ = .ok (.int es.length) := (hL _).2 rfl
    simp only [findLive_saveLive_same hu, Res.ok_bind, Close.arrLen]
    cases op with
    | push | slot _ =>
      simp only [arrLength, lenSucc_eval hL']
      exact Sim.of_eq (by rw [hlen])
    | pop _ =>
      simp only [arrLength, lenPred_eval hL']
      exact Sim.of_eq (by rw [hlen])
  | above =>
    obtain ⟨f, t, rfl⟩ := hr
    obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu
    simp only [arrLength, hf, Res.ok_bind, save_cons_arrLen hs']
    rw [hw₀, Res.ok_bind] at hold
    exact hold
  | diverge => rw [findLive_saveLive_diverge hr hu]; exact hold
  | below rest =>
    obtain ⟨f, t, rfl, hrest⟩ := hr
    rcases below_cases hrest with ⟨g, rest', rfl⟩ | ⟨k, rest', i, rfl, hk, rfl, hr'⟩
    · exact hopq
    · simp only [arrLength]
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind] at hopq ⊢
      rw [SVal.findLive_append, hc, Res.ok_bind] at hold
      exact arrKey_sim hap hk hL hold hopq fun pv _ _ _ =>
        prim_err_sim fun p x h => by simp only [Close.arrLen, reduceCtorEq] at h

theorem arrMap_sim {σ : State} {op : AOp} {wv : Value} {sh : KShape} {L old opq : LTerm}
    {v c c' u : SVal} {ps qs : List Seg}
    (hc : v.findLive ps = .ok c) (hap : op.apply wv c = .ok c') (hu : v.saveLive ps c' = .ok u)
    (hL : Sim (L.eval σ) (Close.arrLen c))
    (hold : Sim (old.eval σ) (v.findLive qs >>= sh.test))
    (hopq : Sim (opq.eval σ) (u.findLive qs >>= sh.test))
    (r : PathRel) (hr : r.Holds σ ps qs) :
    Sim ((arrMap op L old opq r).eval σ) (u.findLive qs >>= sh.test) := by
  cases r with
  | eq =>
    simp only [PathRel.Holds] at hr; subst hr
    obtain ⟨es, sh₀, fx, es', sh', rfl, rfl, -⟩ := AOp.apply_ok hap
    simp only [arrMap, findLive_saveLive_same hu, Res.ok_bind]
    rw [hc, Res.ok_bind] at hold
    cases sh <;> exact hold
  | above =>
    obtain ⟨f, t, rfl⟩ := hr
    obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu
    simp only [arrMap, hf, Res.ok_bind, save_cons_kmapF hs']
    rw [hw₀, Res.ok_bind] at hold
    exact hold
  | diverge => rw [findLive_saveLive_diverge hr hu]; exact hold
  | below rest =>
    obtain ⟨f, t, rfl, hrest⟩ := hr
    rcases below_cases hrest with ⟨g, rest', rfl⟩ | ⟨k, rest', i, rfl, hk, rfl, hr'⟩
    · exact hopq
    · simp only [arrMap]
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind] at hopq ⊢
      rw [SVal.findLive_append, hc, Res.ok_bind] at hold
      exact arrKey_sim hap hk hL hold hopq fun pv _ _ _ =>
        prim_err_sim fun p x h => by cases sh <;> simp only [KShape.test, kmapF, isMapV,
            Bool.false_eq_true, ↓reduceIte, reduceCtorEq, isFixV] at h

/-- No location the read passes an index at is a mapping: what a copy's read
below a key needs to read the source (a mapping met keeps the target's
entries). -/
def NoMapAlong (y : SVal) (segs : List Seg) : Prop :=
  ∀ pre i rest, segs = pre ++ .at i :: rest → ∀ w, y.findLive pre = .ok w → isMapV w = false

theorem overlay_prim_eq (c : SVal) (p : PrimVal) : c.overlay (.prim p) = .prim p := by
  cases c <;> rfl

theorem lookupBy_overlayFields' (ofs : List (Name × SVal)) (f : Name) :
    ∀ ns : List (Name × SVal), lookupBy f (SVal.overlay.overlayFields ofs ns) =
      (lookupBy f ns).map (fun v => match lookupBy f ofs with
        | some o => o.overlay v
        | none => v.strip)
  | [] => rfl
  | (n, w) :: tl => by
    simp only [SVal.overlay.overlayFields, lookupBy]
    split
    · rename_i h; subst h; rfl
    · exact lookupBy_overlayFields' ofs f tl

theorem lookupBy_stripFields (f : Name) : ∀ ns : List (Name × SVal),
    lookupBy f (SVal.strip.stripFields ns) = (lookupBy f ns).map SVal.strip
  | [] => rfl
  | (n, w) :: tl => by
    simp only [SVal.strip.stripFields, lookupBy]
    split
    · rfl
    · exact lookupBy_stripFields f tl

theorem overlayElems_getElem : ∀ (os ns : List SVal) (i : Nat) (h : i < ns.length)
    (h' : i < (SVal.overlay.overlayElems os ns).length),
    ∃ c : SVal, (SVal.overlay.overlayElems os ns)[i] = c.overlay ns[i]
  | o :: os, n :: ns, 0, _, _ => ⟨o, rfl⟩
  | o :: os, n :: ns, i + 1, h, h' => by
    simp only [SVal.overlay.overlayElems, List.getElem_cons_succ]
    exact overlayElems_getElem os ns i (by simpa only [List.length_cons,
        Nat.add_lt_add_iff_right] using h) (by simpa only [SVal.overlay.overlayElems,
            List.length_cons, Nat.add_lt_add_iff_right] using h')
  | [], ns, i, h, h' => by
    simp only [SVal.overlay.overlayElems]
    exact ⟨.prim (.int 0), by rw [prim_overlay]; exact stripElems_getElem ns i h⟩
  | _ :: _, [], i, h, _ => absurd h (by simp only [List.length_nil, Nat.not_lt_zero,
      not_false_eq_true])
where
  stripElems_getElem : ∀ (ns : List SVal) (i : Nat) (h : i < ns.length),
      (SVal.strip.stripElems ns)[i]'(by rw [Close.stripElems_length]; exact h) = ns[i].strip
    | n :: ns, 0, _ => rfl
    | n :: ns, i + 1, h => by
      simp only [SVal.strip.stripElems, List.getElem_cons_succ]
      exact stripElems_getElem ns i (by simpa only [List.length_cons,
          Nat.add_lt_add_iff_right] using h)

theorem NoMapAlong.field {y w : SVal} {f : Name} {r : List Seg} (h : NoMapAlong y (.field f :: r))
    (hw : y.findLive [.field f] = .ok w) : NoMapAlong w r := by
  intro pre i rest he w' hw'
  apply h (.field f :: pre) i rest (by simp only [he, List.cons_append])
  rw [show Seg.field f :: pre = [Seg.field f] ++ pre from rfl, SVal.findLive_append, hw,
    Res.ok_bind, hw']

theorem NoMapAlong.at {y w : SVal} {i : Int} {r : List Seg} (h : NoMapAlong y (.at i :: r))
    (hw : y.findLive [.at i] = .ok w) : NoMapAlong w r := by
  intro pre j rest he w' hw'
  apply h (.at i :: pre) j rest (by simp only [he, List.cons_append])
  rw [show Seg.at i :: pre = [Seg.at i] ++ pre from rfl, SVal.findLive_append, hw,
    Res.ok_bind, hw']

/-- **A copy read below keys reads the source**, where no location the
read passes a key at is a mapping. -/
theorem overlay_findLive_nomap {G : SVal → Res Value} (hG : ∀ c y : SVal, G (c.overlay y) = G y) :
    ∀ (segs : List Seg) (c y : SVal), NoMapAlong y segs →
      ((c.overlay y).findLive segs >>= G) = (y.findLive segs >>= G)
  | [], c, y, _ => by simp only [SVal.findLive_nil, Res.ok_bind, hG]
  | .field f :: r, c, y, hy => by
    cases y with
    | prim p => rw [overlay_prim_eq]
    | map ne nd => cases c <;> simp only [SVal.overlay, SVal.strip, SVal.findLive]
    | struct nfs =>
      cases hl : lookupBy f nfs with
      | none =>
        cases c <;> simp only [SVal.overlay, SVal.strip, SVal.findLive, lookupBy_stripFields, hl,
            Option.map_none, lookupBy_overlayFields']
      | some w =>
        have hw : (SVal.struct nfs).findLive [.field f] = .ok w := by
          simp only [SVal.findLive, hl, SVal.findLive_nil]
        have hy' := hy.field hw
        have hyr : (SVal.struct nfs).findLive (.field f :: r) = w.findLive r := by
          simp only [SVal.findLive, hl]
        rw [hyr]
        cases c with
        | struct ofs =>
          simp only [SVal.overlay, SVal.findLive, lookupBy_overlayFields', hl, Option.map_some]
          split
          · exact overlay_findLive_nomap hG r _ w hy'
          · rw [← prim_overlay (.int 0)]; exact overlay_findLive_nomap hG r _ w hy'
        | prim _ | array _ _ _ | map _ _ =>
          simp only [SVal.overlay, SVal.strip, SVal.findLive, lookupBy_stripFields, hl,
            Option.map_some]
          rw [← prim_overlay (.int 0)]; exact overlay_findLive_nomap hG r _ w hy'
    | array nel nsh nfx =>
      by_cases hf : f = "length"
      · subst hf
        cases c <;> simp only [SVal.overlay, SVal.strip, SVal.findLive, Close.stripElems_length,
            overlayElems_length]
      · cases c <;> simp only [SVal.overlay, SVal.strip, SVal.findLive]
  | .at i :: r, c, y, hy => by
    have hm := hy [] i r rfl y (by cases y <;> rfl)
    cases y with
    | prim p => rw [overlay_prim_eq]
    | map ne nd => simp only [isMapV, Bool.true_eq_false] at hm
    | struct nfs => cases c <;> simp only [SVal.overlay, SVal.strip, SVal.findLive]
    | array nel nsh nfx =>
      have hlen : ∀ os, (SVal.overlay.overlayElems os nel).length = nel.length :=
        fun os => overlayElems_length os nel
      by_cases hi : 0 ≤ i ∧ i.toNat < nel.length
      · have hw : (SVal.array nel nsh nfx).findLive [.at i] = .ok nel[i.toNat] := by
          simp only [SVal.findLive, hi, and_self, ↓reduceDIte, List.get_eq_getElem,
              SVal.findLive_nil]
        have hy' := hy.at hw
        have hyr : (SVal.array nel nsh nfx).findLive (.at i :: r) = nel[i.toNat].findLive r := by
          simp only [SVal.findLive, hi, and_self, ↓reduceDIte, List.get_eq_getElem]
        rw [hyr]
        cases c with
        | array oel osh ofx =>
          have hi' : 0 ≤ i ∧ i.toNat < (SVal.overlay.overlayElems (oel ++ osh) nel).length := by
            rw [hlen]; exact hi
          obtain ⟨c', hc'⟩ := overlayElems_getElem (oel ++ osh) nel i.toNat hi.2 hi'.2
          simp only [SVal.overlay, SVal.findLive, dif_pos hi', List.get_eq_getElem, hc']
          exact overlay_findLive_nomap hG r c' _ hy'
        | prim _ | struct _ | map _ _ =>
          have hi' : 0 ≤ i ∧ i.toNat < (SVal.strip.stripElems nel).length := by
            rw [Close.stripElems_length]; exact hi
          simp only [SVal.overlay, SVal.strip, SVal.findLive, dif_pos hi', List.get_eq_getElem,
            overlayElems_getElem.stripElems_getElem nel i.toNat hi.2]
          rw [← prim_overlay (.int 0)]; exact overlay_findLive_nomap hG r _ _ hy'
      · have hyr : (SVal.array nel nsh nfx).findLive (.at i :: r) = .error .revert := by
          simp only [SVal.findLive, hi, ↓reduceDIte]
        rw [hyr]
        cases c with
        | array oel osh ofx =>
          have hi' : ¬(0 ≤ i ∧ i.toNat < (SVal.overlay.overlayElems (oel ++ osh) nel).length) := by
            rw [hlen]; exact hi
          simp only [SVal.overlay, SVal.findLive, hi', ↓reduceDIte]
        | prim _ | struct _ | map _ _ =>
          have hi' : ¬(0 ≤ i ∧ i.toNat < (SVal.strip.stripElems nel).length) := by
            rw [Close.stripElems_length]; exact hi
          simp only [SVal.overlay, SVal.strip, SVal.findLive, hi', ↓reduceDIte]

theorem NoMapAlong.nil (y : SVal) : NoMapAlong y [] := by
  intro pre i rest he
  cases pre <;> simp only [List.nil_append, List.nil_eq, reduceCtorEq, List.cons_append] at he

theorem NoMapAlong.snoc_field {y : SVal} {p : List Seg} (f : Name) (h : NoMapAlong y p) :
    NoMapAlong y (p ++ [.field f]) := by
  intro pre i rest he w hw
  obtain ⟨rest', rfl⟩ : ∃ rest', p = pre ++ .at i :: rest' := by
    rcases List.eq_nil_or_concat rest with rfl | ⟨r', x, rfl⟩
    · have := congrArg List.getLast? he
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq,
          reduceCtorEq] at this
    · refine ⟨r', ?_⟩
      have := he
      simp only [List.concat_eq_append] at this
      rw [show pre ++ Seg.at i :: (r' ++ [x]) = (pre ++ Seg.at i :: r') ++ [x] by
        simp only [List.append_assoc, List.cons_append]] at this
      exact (List.append_inj' this rfl).1
  exact h pre i rest' rfl w hw

theorem NoMapAlong.snoc_at {y : SVal} {p : List Seg} (i : Int) (h : NoMapAlong y p)
    (hp : ∀ w, y.findLive p = .ok w → isMapV w = false) : NoMapAlong y (p ++ [.at i]) := by
  intro pre j rest he w hw
  rcases List.eq_nil_or_concat rest with rfl | ⟨r', x, rfl⟩
  · have := List.append_inj' he rfl
    obtain ⟨rfl, -⟩ := this
    exact hp w hw
  · have h' := he
    simp only [List.concat_eq_append] at h'
    rw [show pre ++ Seg.at j :: (r' ++ [x]) = (pre ++ Seg.at j :: r') ++ [x] by
      simp only [List.append_assoc, List.cons_append]] at h'
    exact h pre j r' (List.append_inj' h' rfl).1 w hw

/-- **A read below a copy reads the source**, key by key: where the
source has a mapping at a key, the read is kept whole. -/
theorem copyKeys_sim {σ : State} {G : SVal → Res Value} (hG : ∀ c y : SVal, G (c.overlay y) = G y)
    {sv n cur u : SVal} {ps sqs full : List Seg} {srcMap F : List SSeg → LTerm} {opq : LTerm}
    (hn : sv.findLive sqs = .ok n) (hu : u.findLive ps = .ok (cur.overlay n))
    (hM : ∀ pre rs, segsEval σ pre = .ok rs →
      Sim ((srcMap pre).eval σ) (sv.findLive (sqs ++ rs) >>= KShape.map.test))
    (hF : ∀ rest rs, segsEval σ rest = .ok rs → Sim ((F rest).eval σ) (sv.findLive (sqs ++ rs) >>= G))
    (hopq : Sim (opq.eval σ) (u.findLive (ps ++ full) >>= G)) :
    ∀ (r pre : List SSeg) (preS rS : List Seg), segsEval σ pre = .ok preS →
      segsEval σ r = .ok rS → full = preS ++ rS → NoMapAlong n preS →
        Sim ((copyKeys srcMap opq F pre r).eval σ) (u.findLive (ps ++ full) >>= G)
  | [], pre, preS, rS, hpre, hr, hfull, hnm => by
    cases hr
    simp only [List.append_nil] at hfull
    rw [hfull]
    simp only [copyKeys]
    have h := hF pre preS hpre
    rw [SVal.findLive_append, hn, Res.ok_bind, ← overlay_findLive_nomap hG preS cur n hnm] at h
    rw [SVal.findLive_append, hu, Res.ok_bind]
    exact h
  | .field f :: r, pre, preS, rS, hpre, hr, hfull, hnm => by
    obtain ⟨rS', hr', he⟩ := Res.bind_eq_ok.1 hr
    cases he
    simp only [copyKeys]
    exact copyKeys_sim hG hn hu hM hF hopq r (pre ++ [.field f]) (preS ++ [.field f]) rS'
      (segsEval_append σ hpre rfl) hr' (by simp only [hfull, List.append_assoc, List.cons_append,
          List.nil_append]) (hnm.snoc_field f)
  | .key k :: r, pre, preS, rS, hpre, hr, hfull, hnm => by
    obtain ⟨i, hi, hr⟩ := Res.bind_eq_ok.1 hr
    obtain ⟨rS', hr', he⟩ := Res.bind_eq_ok.1 hr
    cases he
    simp only [copyKeys]
    have hm := hM pre preS hpre
    rw [SVal.findLive_append, hn, Res.ok_bind] at hm
    by_cases hmap : ∃ w, n.findLive preS = .ok w ∧ isMapV w = true
    · obtain ⟨w, hw, hwm⟩ := hmap
      have hmt : (srcMap pre).eval σ = .ok (.bool true) := by
        apply (hm _).2
        rw [hw, Res.ok_bind]
        simp only [KShape.test, kmapF, hwm, ↓reduceIte]
      simp only [LTerm.eval, isT_eval, hmt, Res.ok_bind, pickBranch]
      exact hopq
    · have hmt : ∀ x, (srcMap pre).eval σ ≠ .ok x := by
        intro x hx
        have := (hm x).1 hx
        obtain ⟨w, hw, ht⟩ := Res.bind_eq_ok.1 this
        simp only [KShape.test, kmapF] at ht
        split at ht
        · exact hmap ⟨w, hw, ‹_›⟩
        · cases ht
      have hfalse : (isT (srcMap pre)).eval σ = .ok (.bool false) := by
        rw [isT_eval]
        cases hh : (srcMap pre).eval σ with
        | ok x => exact absurd hh (hmt x)
        | error _ => rfl
      simp only [LTerm.eval, hfalse, Res.ok_bind, pickBranch]
      refine copyKeys_sim hG hn hu hM hF hopq r (pre ++ [.key k]) (preS ++ [.at i]) rS'
        (segsEval_append σ hpre (by simp only [segsEval, hi, Res.ok_bind])) hr'
        (by simp only [hfull, List.append_assoc, List.cons_append,
            List.nil_append]) (hnm.snoc_at i fun w hw => ?_)
      cases hb : isMapV w with
      | false => rfl
      | true => exact absurd ⟨w, hw, hb⟩ hmap

theorem copyLeaf_sim {σ : State} {G : SVal → Res Value} (hG : ∀ c y : SVal, G (c.overlay y) = G y)
    {v sv cur n u : SVal} {ps qs sqs : List Seg} {SQ : LPath} {atEq aboveV old opq : LTerm}
    {srcMap F : List SSeg → LTerm}
    (hn : sv.findLive sqs = .ok n) (hsq : SQ.eval σ = .ok sqs)
    (hu : v.saveLive ps (cur.overlay n) = .ok u)
    (heq : Sim (atEq.eval σ) (G n))
    (habove : ∀ f t, ps = qs ++ f :: t → Sim (aboveV.eval σ) (u.findLive qs >>= G))
    (hold : Sim (old.eval σ) (v.findLive qs >>= G))
    (hopq : Sim (opq.eval σ) (u.findLive qs >>= G))
    (hM : ∀ pre q', (SQ.addSegs pre).eval σ = .ok q' →
      Sim ((srcMap pre).eval σ) (sv.findLive q' >>= KShape.map.test))
    (hF : ∀ rest q', (SQ.addSegs rest).eval σ = .ok q' →
      Sim ((F rest).eval σ) (sv.findLive q' >>= G))
    (r : PathRel) (hr : r.Holds σ ps qs) :
    Sim ((copyLeaf atEq aboveV old opq srcMap F r).eval σ) (u.findLive qs >>= G) := by
  cases r with
  | eq =>
    simp only [PathRel.Holds] at hr; subst hr
    simp only [copyLeaf, findLive_saveLive_same hu, Res.ok_bind, hG]
    exact heq
  | above =>
    obtain ⟨f, t, rfl⟩ := hr
    exact habove f t rfl
  | diverge => rw [findLive_saveLive_diverge hr hu]; exact hold
  | below rest =>
    obtain ⟨f, t, rfl, hrest⟩ := hr
    simp only [copyLeaf]
    have hseg : ∀ xs rs, segsEval σ xs = .ok rs → (SQ.addSegs xs).eval σ = .ok (sqs ++ rs) := by
      intro xs rs h; rw [LPath.addSegs_eval, hsq, Res.ok_bind, h, Res.ok_bind]
    exact copyKeys_sim hG hn (findLive_saveLive_same hu)
      (fun pre rs h => hM pre _ (hseg pre rs h)) (fun rest rs h => hF rest _ (hseg rest rs h))
      hopq rest [] [] (f :: t) rfl hrest rfl (NoMapAlong.nil n)

theorem copy_eval_ok {σ : State} {s src : LStor} {P SQ : LPath} {u : SVal}
    (hu : (LStor.copy s P src SQ).eval σ = .ok u) :
    ∃ sv sqs n v ps cur, src.eval σ = .ok sv ∧ SQ.eval σ = .ok sqs ∧ sv.findLive sqs = .ok n ∧
      s.eval σ = .ok v ∧ P.eval σ = .ok ps ∧ v.findLive ps = .ok cur ∧
      v.saveLive ps (cur.overlay n) = .ok u := by
  simp only [LStor.eval, Res.bind_eq_ok] at hu
  obtain ⟨sv, h1, sqs, h2, n, h3, v, h4, ps, h5, cur, h6, h7⟩ := hu
  exact ⟨sv, sqs, n, v, ps, cur, h1, h2, h3, h4, h5, h6, h7⟩

theorem arr_eval_ok {σ : State} {op : AOp} {s : LStor} {P : LPath} {w : LTerm} {u : SVal}
    (hu : (LStor.arr op s P w).eval σ = .ok u) :
    ∃ wv v ps c c', w.eval σ = .ok wv ∧ s.eval σ = .ok v ∧ P.eval σ = .ok ps ∧
      v.findLive ps = .ok c ∧ op.apply wv c = .ok c' ∧ v.saveLive ps c' = .ok u := by
  simp only [LStor.eval, Res.bind_eq_ok] at hu
  obtain ⟨wv, h1, v, h2, ps, h3, c, h4, c', h5, h6⟩ := hu
  exact ⟨wv, v, ps, c, c', h1, h2, h3, h4, h5, h6⟩

section Wrappers

variable {σ : State} {s src : LStor} {P SQ Q : LPath} {u : SVal} {qs : List Seg}

theorem copy_readU_sim (hu : (LStor.copy s P src SQ).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ)) (hSQ : Sim (SQ.elim.eval σ) (SQ.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue))
    (ihS : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.readU Q').eval σ) (v.findLive qs >>= SVal.asValue))
    (ihSM : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.mapU .map Q').eval σ) (v.findLive qs >>= KShape.map.test)) :
    Sim (((LStor.copy s P src SQ).readU Q).eval σ) (u.findLive qs >>= SVal.asValue) := by
  obtain ⟨sv, sqs, n, v, ps, cur, hsv, hsq, hn, hv, hp, hc, hu'⟩ := copy_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hsq' : SQ.elim.eval σ = .ok sqs := (hSQ sqs).2 hsq
  rw [LStor.readU]
  refine cmp_sim hp' hq fun r hr => copyLeaf_sim (G := SVal.asValue) overlay_asValue hn hsq' hu'
    ?_ ?_ (ihR hv hq) ?_ (fun pre q' hq' => ihSM _ hsv hq') (fun rest q' hq' => ihS _ hsv hq') r hr
  · have := ihS SQ.elim hsv hsq'; rwa [hn, Res.ok_bind] at this
  · intro f t he; subst he
    obtain ⟨_, w', _, hs', hf⟩ := save_through qs (f :: t) hu'
    obtain ⟨e, he⟩ := save_cons_asValue hs'
    exact Sim.halt (by simp only [LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
        implies_true]) (by simp only [hf, Res.ok_bind, he, ne_eq, reduceCtorEq, not_false_eq_true,
            implies_true])
  · exact Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind])

theorem copy_hasU_sim (hu : (LStor.copy s P src SQ).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ)) (hSQ : Sim (SQ.elim.eval σ) (SQ.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true)))
    (ihS : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.hasU Q').eval σ) (v.findLive qs >>= fun _ => .ok (.bool true)))
    (ihSM : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.mapU .map Q').eval σ) (v.findLive qs >>= KShape.map.test)) :
    Sim (((LStor.copy s P src SQ).hasU Q).eval σ) (u.findLive qs >>= fun _ => .ok (.bool true)) := by
  obtain ⟨sv, sqs, n, v, ps, cur, hsv, hsq, hn, hv, hp, hc, hu'⟩ := copy_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hsq' : SQ.elim.eval σ = .ok sqs := (hSQ sqs).2 hsq
  rw [LStor.hasU]
  refine cmp_sim hp' hq fun r hr => copyLeaf_sim (G := fun _ => .ok (.bool true))
    (fun _ _ => rfl) hn hsq' hu' (Sim.of_eq rfl) ?_ (ihR hv hq) ?_
    (fun pre q' hq' => ihSM _ hsv hq') (fun rest q' hq' => ihS _ hsv hq') r hr
  · intro f t he; subst he
    obtain ⟨_, w', _, _, hf⟩ := save_through qs (f :: t) hu'
    exact Sim.of_eq (by simp only [LTerm.eval, hf, Res.ok_bind])
  · exact Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind])

theorem copy_lenU_sim (hu : (LStor.copy s P src SQ).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ)) (hSQ : Sim (SQ.elim.eval σ) (SQ.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen))
    (ihS : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.lenU Q').eval σ) (v.findLive qs >>= Close.arrLen))
    (ihSM : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.mapU .map Q').eval σ) (v.findLive qs >>= KShape.map.test)) :
    Sim (((LStor.copy s P src SQ).lenU Q).eval σ) (u.findLive qs >>= Close.arrLen) := by
  obtain ⟨sv, sqs, n, v, ps, cur, hsv, hsq, hn, hv, hp, hc, hu'⟩ := copy_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hsq' : SQ.elim.eval σ = .ok sqs := (hSQ sqs).2 hsq
  rw [LStor.lenU]
  refine cmp_sim hp' hq fun r hr => copyLeaf_sim (G := Close.arrLen) overlay_arrLen hn hsq' hu'
    ?_ ?_ (ihR hv hq) ?_ (fun pre q' hq' => ihSM _ hsv hq') (fun rest q' hq' => ihS _ hsv hq') r hr
  · have := ihS SQ.elim hsv hsq'; rwa [hn, Res.ok_bind] at this
  · intro f t he; subst he
    obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu'
    have hold := ihR hv hq
    rw [hw₀, Res.ok_bind] at hold
    rw [hf, Res.ok_bind, save_cons_arrLen hs']
    exact hold
  · exact Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind])

theorem copy_mapU_sim {sh : KShape} (hu : (LStor.copy s P src SQ).eval σ = .ok u)
    (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ)) (hSQ : Sim (SQ.elim.eval σ) (SQ.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test))
    (ihS : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.mapU sh Q').eval σ) (v.findLive qs >>= sh.test))
    (ihSM : ∀ (Q' : LPath) {v qs}, src.eval σ = .ok v → Q'.eval σ = .ok qs →
      Sim ((src.mapU .map Q').eval σ) (v.findLive qs >>= KShape.map.test)) :
    Sim (((LStor.copy s P src SQ).mapU sh Q).eval σ) (u.findLive qs >>= sh.test) := by
  obtain ⟨sv, sqs, n, v, ps, cur, hsv, hsq, hn, hv, hp, hc, hu'⟩ := copy_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hsq' : SQ.elim.eval σ = .ok sqs := (hSQ sqs).2 hsq
  rw [LStor.mapU]
  refine cmp_sim hp' hq fun r hr => copyLeaf_sim (G := sh.test) (overlay_test sh) hn hsq' hu'
    ?_ ?_ (ihR hv hq) ?_ (fun pre q' hq' => ihSM _ hsv hq') (fun rest q' hq' => ihS _ hsv hq') r hr
  · have := ihS SQ.elim hsv hsq'; rwa [hn, Res.ok_bind] at this
  · intro f t he; subst he
    obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu'
    have hold := ihR hv hq
    rw [hw₀, Res.ok_bind] at hold
    rw [hf, Res.ok_bind, save_cons_kmapF hs']
    exact hold
  · exact Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind])

variable {op : AOp} {w : LTerm}

theorem arr_readU_sim (hu : (LStor.arr op s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ)) (hw : Sim (w.elim.eval σ) (w.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue))
    (ihL : ∀ {v ps}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      Sim ((s.lenU P.elim).eval σ) (v.findLive ps >>= Close.arrLen))
    (ihS : ∀ (rest : List SSeg) (opq : LTerm) {v : SVal} {ps : List Seg} {es sh : List SVal}
      {fx : Bool} {R : RefTy} {r : List Seg}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      v.findLive ps = .ok (.array es sh fx) → segsEval σ rest = .ok r →
      Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) →
      Sim ((s.slotU P.elim rest opq).eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue)) :
    Sim (((LStor.arr op s P w).readU Q).eval σ) (u.findLive qs >>= SVal.asValue) := by
  obtain ⟨wv, v, ps, c, c', hw₀, hv, hp, hc, hap, hu'⟩ := arr_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hL := ihL hv hp'
  rw [hc, Res.ok_bind] at hL
  rw [LStor.readU]
  exact cmp_sim hp' hq fun r hr => arrRead_sim hc hap hu' ((hw wv).2 hw₀) hL (ihR hv hq)
    (Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind]))
    (fun es sh fx R hce _ rest r hr hopq => ihS rest _ hv hp' (hce ▸ hc) hr hopq) r hr

theorem arr_hasU_sim (hu : (LStor.arr op s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true)))
    (ihL : ∀ {v ps}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      Sim ((s.lenU P.elim).eval σ) (v.findLive ps >>= Close.arrLen)) :
    Sim (((LStor.arr op s P w).hasU Q).eval σ) (u.findLive qs >>= fun _ => .ok (.bool true)) := by
  obtain ⟨wv, v, ps, c, c', hw₀, hv, hp, hc, hap, hu'⟩ := arr_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hL := ihL hv hp'
  rw [hc, Res.ok_bind] at hL
  rw [LStor.hasU]
  exact cmp_sim hp' hq fun r hr => arrHas_sim hc hap hu' hL (ihR hv hq)
    (Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind])) r hr

theorem arr_lenU_sim (hu : (LStor.arr op s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen))
    (ihL : ∀ {v ps}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      Sim ((s.lenU P.elim).eval σ) (v.findLive ps >>= Close.arrLen)) :
    Sim (((LStor.arr op s P w).lenU Q).eval σ) (u.findLive qs >>= Close.arrLen) := by
  obtain ⟨wv, v, ps, c, c', hw₀, hv, hp, hc, hap, hu'⟩ := arr_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hL := ihL hv hp'
  rw [hc, Res.ok_bind] at hL
  rw [LStor.lenU]
  exact cmp_sim hp' hq fun r hr => arrLength_sim hc hap hu' hL (ihR hv hq)
    (Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind])) r hr

theorem arr_mapU_sim {sh : KShape} (hu : (LStor.arr op s P w).eval σ = .ok u)
    (hq : Q.eval σ = .ok qs) (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test))
    (ihL : ∀ {v ps}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      Sim ((s.lenU P.elim).eval σ) (v.findLive ps >>= Close.arrLen)) :
    Sim (((LStor.arr op s P w).mapU sh Q).eval σ) (u.findLive qs >>= sh.test) := by
  obtain ⟨wv, v, ps, c, c', hw₀, hv, hp, hc, hap, hu'⟩ := arr_eval_ok hu
  have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
  have hL := ihL hv hp'
  rw [hc, Res.ok_bind] at hL
  rw [LStor.mapU]
  exact cmp_sim hp' hq fun r hr => arrMap_sim hc hap hu' hL (ihR hv hq)
    (Sim.of_eq (by simp only [LTerm.eval, hu, hq, Res.ok_bind])) r hr

end Wrappers

theorem arrOk_sim {σ : State} {op : AOp} {wv : Value} {L : LTerm} {x : Res SVal}
    (hL : Sim (L.eval σ) (x >>= Close.arrLen)) :
    Sim ((arrOk op L).eval σ) (x >>= fun c => op.apply wv c >>= fun _ => .ok (.bool true)) := by
  have hno : (∀ y, x >>= Close.arrLen ≠ .ok y) → Sim ((arrOk op L).eval σ)
      (x >>= fun c => op.apply wv c >>= fun _ => .ok (.bool true)) := by
    intro hx
    have hLn : ∀ y, L.eval σ ≠ .ok y := fun y h => hx y ((hL y).1 h)
    refine Sim.halt ?_ ?_
    · intro a ha
      obtain ⟨e, he⟩ : ∃ e, L.eval σ = .error e := by
        cases h : L.eval σ with
        | ok y => exact absurd h (hLn y)
        | error e => exact ⟨e, rfl⟩
      cases op <;> simp only [arrOk, LTerm.eval, bind, Except.bind, he, reduceCtorEq,
          evalBinop] at ha
    · intro a ha
      obtain ⟨c, hc, ha⟩ := Res.bind_eq_ok.1 ha
      obtain ⟨c', hap, -⟩ := Res.bind_eq_ok.1 ha
      obtain ⟨es, sh, fx, _, _, rfl, -⟩ := AOp.apply_ok hap
      exact hx _ (by rw [hc, Res.ok_bind]; rfl)
  cases x with
  | error e => exact hno fun y h => by simp only [Res.error_bind, reduceCtorEq] at h
  | ok c =>
    cases c with
    | array es sh fx =>
      have hL' : L.eval σ = .ok (.int es.length) := (hL _).2 rfl
      cases op with
      | push | slot _ => exact Sim.of_eq (by simp only [arrOk, LTerm.eval, hL', Res.ok_bind,
          AOp.apply])
      | pop keep =>
        rcases hr : es.reverse with _ | ⟨l, rr⟩
        · have : es = [] := List.reverse_eq_nil_iff.1 hr
          subst this
          refine Sim.halt ?_ ?_ <;>
            simp only [arrOk, LTerm.eval, bind, Except.bind, evalBinop, hL', List.length_nil,
                Int.cast_ofNat_Int, applyBinOp, Value.asInt, Int.lt_irrefl, decide_false,
                    checkArith, pickBranch, ne_eq, reduceCtorEq, not_false_eq_true, implies_true,
                    AOp.apply, List.reverse_nil]
        · have hlen : es.length = rr.length + 1 := by
            rw [← List.length_reverse, hr]; rfl
          refine Sim.of_eq ?_
          simp only [arrOk, LTerm.eval, bind, Except.bind, evalBinop, hL', hlen, Int.natCast_add,
              Int.cast_ofNat_Int, applyBinOp, Value.asInt, Int.succ_ofNat_pos, decide_true,
                  checkArith, pickBranch, AOp.apply, hr]
    | prim _ | struct _ | map _ _ => exact hno fun y h => by simp only [Res.ok_bind, Close.arrLen,
        reduceCtorEq] at h

theorem arr_okE_sim {σ : State} {op : AOp} {s : LStor} {P : LPath} {w : LTerm}
    (hs : Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true)))
    (hw : Sim (w.elim.eval σ) (w.eval σ)) (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihL : ∀ {v ps}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      Sim ((s.lenU P.elim).eval σ) (v.findLive ps >>= Close.arrLen)) :
    Sim ((LStor.arr op s P w).okE.eval σ)
      ((LStor.arr op s P w).eval σ >>= fun _ => .ok (.bool true)) := by
  simp only [LStor.okE]
  split
  · rename_i hn
    intro a
    simp only [LTerm.eval, LStor.eval, Res.bind_eq_ok]
    constructor
    · rintro ⟨_, h₁, wv, h₂, _, ⟨ps, h₃, -⟩, h₄⟩
      obtain ⟨v, hv, -⟩ := Res.bind_eq_ok.1 ((hs _).1 h₁)
      have hok := ((arrOk_sim (op := op) (wv := wv) (ihL hv h₃)) a).1 h₄
      obtain ⟨c, hc, h₅⟩ := Res.bind_eq_ok.1 hok
      obtain ⟨c', hap, h₆⟩ := Res.bind_eq_ok.1 h₅
      have hq := (hP ps).1 h₃
      obtain ⟨u, hu⟩ := (save_ok_iff_find_ok (new := c') (LPath.noLen_eval σ hn hq)).2 ⟨_, hc⟩
      exact ⟨u, ⟨wv, (hw wv).1 h₂, v, hv, ps, hq, c, hc, c', hap, hu⟩, h₆⟩
    · rintro ⟨u, ⟨wv, h₂, v, hv, ps, hq, c, hc, c', hap, hu⟩, h₆⟩
      have h₃ := (hP ps).2 hq
      refine ⟨.bool true, (hs _).2 (by simp only [hv, Res.ok_bind]), wv, (hw wv).2 h₂, .bool true,
        ⟨ps, h₃, rfl⟩, ?_⟩
      exact ((arrOk_sim (wv := wv) (ihL hv h₃)) _).2 (by simpa only [hc, Res.ok_bind, hap,
          Except.ok.injEq] using h₆)
  · exact Sim.refl _

theorem copy_okE_sim {σ : State} {s src : LStor} {P SQ : LPath}
    (hs : Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true)))
    (hsrc : Sim (src.okE.eval σ) (src.eval σ >>= fun _ => .ok (.bool true)))
    (hP : Sim (P.elim.eval σ) (P.eval σ)) (hSQ : Sim (SQ.elim.eval σ) (SQ.eval σ))
    (ihH : ∀ {v ps}, s.eval σ = .ok v → P.elim.eval σ = .ok ps →
      Sim ((s.hasU P.elim).eval σ) (v.findLive ps >>= fun _ => .ok (.bool true)))
    (ihS : ∀ {v ps}, src.eval σ = .ok v → SQ.elim.eval σ = .ok ps →
      Sim ((src.hasU SQ.elim).eval σ) (v.findLive ps >>= fun _ => .ok (.bool true))) :
    Sim ((LStor.copy s P src SQ).okE.eval σ)
      ((LStor.copy s P src SQ).eval σ >>= fun _ => .ok (.bool true)) := by
  simp only [LStor.okE]
  split
  · rename_i hn
    intro a
    simp only [LTerm.eval, LStor.eval, Res.bind_eq_ok]
    constructor
    · rintro ⟨_, h₁, _, ⟨sqs, h₂, -⟩, _, h₃, _, h₄, _, ⟨ps, h₅, -⟩, h₆⟩
      obtain ⟨sv, hsv, -⟩ := Res.bind_eq_ok.1 ((hsrc _).1 h₁)
      obtain ⟨n, hn', -⟩ := Res.bind_eq_ok.1 ((ihS hsv h₂ _).1 h₃)
      obtain ⟨v, hv, -⟩ := Res.bind_eq_ok.1 ((hs _).1 h₄)
      obtain ⟨cur, hc, he⟩ := Res.bind_eq_ok.1 ((ihH hv h₅ _).1 h₆)
      cases he
      have hq := (hP ps).1 h₅
      obtain ⟨u, hu⟩ := (save_ok_iff_find_ok (new := cur.overlay n)
        (LPath.noLen_eval σ hn hq)).2 ⟨_, hc⟩
      exact ⟨u, ⟨sv, hsv, sqs, (hSQ sqs).1 h₂, n, hn', v, hv, ps, hq, cur, hc, hu⟩, rfl⟩
    · rintro ⟨u, ⟨sv, hsv, sqs, hsq, n, hn', v, hv, ps, hq, cur, hc, hu⟩, he⟩
      cases he
      have h₂ := (hSQ sqs).2 hsq
      have h₅ := (hP ps).2 hq
      exact ⟨.bool true, (hsrc _).2 (by simp only [hsv, Res.ok_bind]), .bool true, ⟨sqs, h₂, rfl⟩,
        .bool true, (ihS hsv h₂ _).2 (by simp only [hn', Res.ok_bind]), .bool true,
        (hs _).2 (by simp only [hv, Res.ok_bind]), .bool true, ⟨ps, h₅, rfl⟩,
        (ihH hv h₅ _).2 (by simp only [hc, Res.ok_bind])⟩
  · exact Sim.refl _

/-! ### The slot a `push()` recycles -/

theorem pushSlot_ref_cons (R : RefTy) (c : SVal) (t : List SVal) :
    (pushSlot (.ref R) (c :: t)).1 = c := by
  simp only [pushSlot, Ty.isPrimitive, Bool.false_eq_true, ↓reduceIte]

theorem AOp.apply_pop_eq {keep : Bool} {wv : Value} {c c' : SVal}
    (h : (AOp.pop keep).apply wv c = .ok c') :
    ∃ es last sh fx, c = .array (es ++ [last]) sh fx ∧
      c' = .array es ((if keep then last else last.defaultOf) :: sh) fx := by
  cases c with
  | array elems shadow fx =>
    simp only [AOp.apply] at h
    rcases hr : elems.reverse with _ | ⟨l, rr⟩ <;> simp only [hr] at h
    · cases h
    · cases h
      refine ⟨rr.reverse, l, shadow, fx, ?_, rfl⟩
      have he : elems = (l :: rr).reverse := by rw [← hr, List.reverse_reverse]
      simp only [he, List.reverse_cons]
  | prim _ | struct _ | map _ _ => simp only [apply, reduceCtorEq] at h

/-- **The default of an element, read below it**: the leaf a `delete` of
the element at `E` leaves, at `rest`. -/
theorem delSlot_sim {σ : State} {s : LStor} {v e : SVal} {E : LPath} {eps : List Seg}
    {rest : List SSeg} {r : List Seg}
    (hE : E.eval σ = .ok eps) (he : v.findLive eps = .ok e) (hr : segsEval σ rest = .ok r)
    (ihR : ∀ (Q : LPath) {qs}, Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue))
    (ihM : ∀ (sh : KShape) (Q : LPath) {qs}, Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    Sim ((delLeaf (s.readU (E.addSegs rest)) E (fun sh q => s.mapU sh q)
      (if rest.isEmpty then .eq else .below rest)).eval σ)
      (e.defaultOf.findLive r >>= SVal.asValue) := by
  have hQ : (E.addSegs rest).eval σ = .ok (eps ++ r) := by
    rw [LPath.addSegs_eval, hE, Res.ok_bind, hr, Res.ok_bind]
  have hold := ihR _ hQ
  by_cases hemp : rest.isEmpty = true
  · have hr0 : r = [] := (segsEval_isEmpty hr).1 hemp
    subst hr0
    rw [if_pos hemp]
    simp only [delLeaf, LTerm.eval, SVal.findLive_nil, Res.ok_bind, asValue_defaultOf]
    rw [List.append_nil, he, Res.ok_bind] at hold
    exact Sim.bind hold fun _ => Sim.refl _
  · rw [if_neg hemp]
    simp only [delLeaf]
    have hEnd : Sim ((LTerm.zero (s.readU (E.addSegs rest))).eval σ)
        (v.findLive (eps ++ r) >>= fun w => w.defaultOf.asValue) := by
      simp only [LTerm.eval]
      refine (Sim.bind hold (fun _ => Sim.refl _)).trans (Sim.of_eq ?_)
      rw [bind_assoc]; congr 1; funext w; rw [asValue_defaultOf]
    have h := delBelow_sim (v := v) (G := SVal.asValue)
      (fun sh q qs hq' => ihM sh q hq') hold hEnd rest E eps r hE hr rfl
    rw [he, Res.ok_bind] at h
    exact h

theorem pop_slotU_sim {σ : State} {keep : Bool} {s : LStor} {P' P : LPath} {w' opq : LTerm}
    {rest : List SSeg} {v : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool} {R : RefTy}
    {r : List Seg}
    (hu : (LStor.arr (.pop keep) s P' w').eval σ = .ok v) (hP' : Sim (P'.elim.eval σ) (P'.eval σ))
    (hp : P.eval σ = .ok ps) (hn : v.findLive ps = .ok (.array es sh fx))
    (hr : segsEval σ rest = .ok r)
    (hopq : Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue))
    (ihR : ∀ (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test))
    (ihL : ∀ {v qs}, s.eval σ = .ok v → P.eval σ = .ok qs →
      Sim ((s.lenU P).eval σ) (v.findLive qs >>= Close.arrLen)) :
    Sim (((LStor.arr (.pop keep) s P' w').slotU P rest opq).eval σ)
      ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) := by
  rw [LStor.slotU]
  split
  · rename_i heq
    have hPe : P'.elim = P := by simpa only [beq_iff_eq] using heq
    obtain ⟨wv, v', ps', c0, c1, -, hv', hp', hc0, hap, hu'⟩ := arr_eval_ok hu
    have hpp : ps' = ps := by
      have := (hP' ps').2 hp'
      rw [hPe, hp] at this
      cases this; rfl
    subst hpp
    rw [findLive_saveLive_same hu'] at hn
    obtain ⟨es0, last, sh0, fx0, rfl, rfl⟩ := AOp.apply_pop_eq hap
    simp only [Except.ok.injEq, SVal.array.injEq] at hn
    obtain ⟨rfl, rfl, rfl⟩ := hn
    rw [pushSlot_ref_cons] at hopq ⊢
    have hL := ihL hv' hp
    rw [hc0, Res.ok_bind] at hL
    have hL' : (s.lenU P).eval σ = .ok (.int (es0 ++ [last]).length) := (hL _).2 rfl
    have hE : (P.at (lenPred (s.lenU P))).eval σ = .ok (ps' ++ [.at es0.length]) := by
      simp only [LPath.eval, hp, Res.ok_bind, lenPred_eval hL', Value.asInt]
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
          Int.natCast_add, Int.cast_ofNat_Int, Int.add_sub_cancel]
    have he : v'.findLive (ps' ++ [.at es0.length]) = .ok last := by
      rw [SVal.findLive_append, hc0, Res.ok_bind, findLive_last]
    cases keep
    · simp only [Bool.false_eq_true, if_false]
      exact delSlot_sim hE he hr (fun Q _ hq => ihR Q hv' hq) (fun sh Q _ hq => ihM sh Q hv' hq)
    · simp only [if_true]
      have hQ : ((P.at (lenPred (s.lenU P))).addSegs rest).eval σ =
          .ok ((ps' ++ [.at es0.length]) ++ r) := by
        rw [LPath.addSegs_eval, hE, Res.ok_bind, hr, Res.ok_bind]
      have := ihR _ hv' hQ
      rw [SVal.findLive_append, he, Res.ok_bind] at this
      exact this
  · exact hopq

theorem del_slotU_sim {σ : State} {s : LStor} {P' P : LPath} {opq : LTerm}
    {rest : List SSeg} {v : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool} {R : RefTy}
    {r : List Seg}
    (hu : (LStor.del s P').eval σ = .ok v) (hP' : Sim (P'.elim.eval σ) (P'.eval σ))
    (hp : P.eval σ = .ok ps) (hn : v.findLive ps = .ok (.array es sh fx))
    (hr : segsEval σ rest = .ok r)
    (hopq : Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue))
    (ihR : ∀ (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test))
    (ihL : ∀ {v qs}, s.eval σ = .ok v → P.eval σ = .ok qs →
      Sim ((s.lenU P).eval σ) (v.findLive qs >>= Close.arrLen)) :
    Sim (((LStor.del s P').slotU P rest opq).eval σ)
      ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) := by
  rw [LStor.slotU]
  split
  · rename_i heq
    have hPe : P'.elim = P := by simpa only [beq_iff_eq] using heq
    obtain ⟨v', hv', hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps', hp', hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨c0, hc0, hu'⟩ := Res.bind_eq_ok.1 hu
    have hpp : ps' = ps := by
      have := (hP' ps').2 hp'
      rw [hPe, hp] at this
      cases this; rfl
    subst hpp
    rw [findLive_saveLive_same hu'] at hn
    have hM := ihM .fixed P hv' hp
    rw [hc0, Res.ok_bind] at hM
    have hL := ihL hv' hp
    rw [hc0, Res.ok_bind] at hL
    cases c0 with
    | array es0 sh0 fx0 =>
      cases fx0 with
      | true =>
        have hm : (s.mapU .fixed P).eval σ = .ok (.bool true) := (hM _).2 rfl
        simp only [LTerm.eval, isT_eval, hm, Res.ok_bind, pickBranch]
        exact hopq
      | false =>
        have hm : ∀ x, (s.mapU .fixed P).eval σ ≠ .ok x := fun x h => by
          have := (hM x).1 h
          simp only [KShape.test, isFixV, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at this
        have hmT : (isT (s.mapU .fixed P)).eval σ = .ok (.bool false) := by
          rw [isT_eval]
          cases hh : (s.mapU .fixed P).eval σ with
          | ok x => exact absurd hh (hm x)
          | error _ => rfl
        have hL' : (s.lenU P).eval σ = .ok (.int es0.length) := (hL _).2 rfl
        simp only [LTerm.eval, hmT, Res.ok_bind, pickBranch, hL', Value.asInt]
        simp only [SVal.defaultOf, Except.ok.injEq, SVal.array.injEq] at hn
        obtain ⟨rfl, rfl, rfl⟩ := hn
        cases es0 with
        | nil =>
          simp only [List.length_nil, Int.natCast_zero, if_true]
          exact hopq
        | cons e et =>
          have hne : ((e :: et).length : Int) ≠ 0 := by simp only [List.length_cons,
              Int.natCast_add, Int.cast_ofNat_Int, ne_eq]; omega
          rw [if_neg hne]
          simp only [SVal.defaultOf.defaultOfElems, List.cons_append] at hopq ⊢
          rw [pushSlot_ref_cons]
          have hE : (P.at (.lit (.int 0))).eval σ = .ok (ps' ++ [.at 0]) := by
            simp only [LPath.eval, hp, LTerm.eval, Res.ok_bind, Value.asInt]
          have he : v'.findLive (ps' ++ [.at 0]) = .ok e := by
            rw [SVal.findLive_append, hc0, Res.ok_bind]
            simp only [SVal.findLive, Int.le_refl, Int.toNat_zero, List.length_cons,
                Nat.zero_lt_succ, and_self, ↓reduceDIte, Fin.zero_eta, List.get_eq_getElem,
                    Fin.val_zero, List.getElem_cons_zero, SVal.findLive_nil]
          exact delSlot_sim hE he hr (fun Q _ hq => ihR Q hv' hq) (fun sh Q _ hq => ihM sh Q hv' hq)
    | prim p => cases p <;> simp only [SVal.defaultOf, Except.ok.injEq, reduceCtorEq] at hn
    | struct _ => simp only [SVal.defaultOf, Except.ok.injEq, reduceCtorEq] at hn
    | map _ _ => simp only [SVal.defaultOf, Except.ok.injEq, reduceCtorEq] at hn
  · exact hopq

/-! ### Writes and deletes, one lemma per case

The cases of the elimination's soundness, each with what it needs of the
storage below it as hypotheses, so that the mutual proof only dispatches. -/

theorem save_okE_sim {σ : State} {s : LStor} {q : LPath} {w : LTerm}
    (hs : Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true)))
    (hW : Sim (w.elim.eval σ) (w.eval σ))
    (hP : Sim (q.elim.eval σ) (q.eval σ))
    (ihH : ∀ {v qs}, s.eval σ = .ok v → q.elim.eval σ = .ok qs →
      Sim ((s.hasU q.elim).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true))) :
    Sim ((LStor.save s q w).okE.eval σ) ((LStor.save s q w).eval σ >>= fun _ => .ok (.bool true)) := by
    simp only [LStor.okE]
    split
    · rename_i hn
      intro a
      simp only [LTerm.eval, LStor.eval, Res.bind_eq_ok]
      constructor
      · rintro ⟨_, h₁, wv, h₂, _, ⟨qs, h₃, -⟩, h₄⟩
        obtain ⟨v, hv, -⟩ := Res.bind_eq_ok.1 ((hs _).1 h₁)
        have hq := (hP qs).1 h₃
        obtain ⟨_, hf, he⟩ := Res.bind_eq_ok.1 ((ihH hv h₃ a).1 h₄)
        cases he
        obtain ⟨u, hu⟩ := (save_ok_iff_find_ok (new := wv.toSVal) (LPath.noLen_eval σ hn hq)).2
          ⟨_, hf⟩
        exact ⟨u, ⟨wv, (hW wv).1 h₂, v, hv, qs, hq, hu⟩, rfl⟩
      · rintro ⟨u, ⟨wv, h₂, v, hv, qs, hq, hu⟩, he⟩
        cases he
        have h₃ := (hP qs).2 hq
        obtain ⟨c, hc⟩ := (save_ok_iff_find_ok (LPath.noLen_eval σ hn hq)).1 ⟨u, hu⟩
        refine ⟨.bool true, (hs _).2 (by simp only [hv, Res.ok_bind]), wv,
          (hW wv).2 h₂, .bool true, ⟨qs, h₃, rfl⟩, ?_⟩
        exact (ihH hv h₃ _).2 (by simp only [hc, Res.ok_bind])
    · exact Sim.refl _

theorem del_okE_sim {σ : State} {s : LStor} {q : LPath}
    (hs : Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true)))
    (hP : Sim (q.elim.eval σ) (q.eval σ))
    (ihH : ∀ {v qs}, s.eval σ = .ok v → q.elim.eval σ = .ok qs →
      Sim ((s.hasU q.elim).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true))) :
    Sim ((LStor.del s q).okE.eval σ) ((LStor.del s q).eval σ >>= fun _ => .ok (.bool true)) := by
    simp only [LStor.okE]
    split
    · rename_i hn
      intro a
      simp only [LTerm.eval, LStor.eval, Res.bind_eq_ok]
      constructor
      · rintro ⟨_, h₁, _, ⟨qs, h₃, -⟩, h₄⟩
        obtain ⟨v, hv, -⟩ := Res.bind_eq_ok.1 ((hs _).1 h₁)
        have hq := (hP qs).1 h₃
        obtain ⟨c, hf, he⟩ := Res.bind_eq_ok.1 ((ihH hv h₃ a).1 h₄)
        cases he
        obtain ⟨u, hu⟩ := (save_ok_iff_find_ok (new := c.defaultOf) (LPath.noLen_eval σ hn hq)).2
          ⟨_, hf⟩
        exact ⟨u, ⟨v, hv, qs, hq, c, hf, hu⟩, rfl⟩
      · rintro ⟨u, ⟨v, hv, qs, hq, c, hc, hu⟩, he⟩
        cases he
        have h₃ := (hP qs).2 hq
        refine ⟨.bool true, (hs _).2 (by simp only [hv, Res.ok_bind]), .bool true,
          ⟨qs, h₃, rfl⟩, ?_⟩
        exact (ihH hv h₃ _).2 (by simp only [hc, Res.ok_bind])
    · exact Sim.refl _

theorem save_readU_sim {σ : State} {s : LStor} {P Q : LPath} {w : LTerm} {u : SVal} {qs : List Seg}
    (hu : (LStor.save s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (hW : Sim (w.elim.eval σ) (w.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue)) :
    Sim (((LStor.save s P w).readU Q).eval σ) (u.findLive qs >>= SVal.asValue) := by
    obtain ⟨wv, hw, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    rw [LStor.readU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      simp only [saveLeaf, findLive_saveLive_same hu, Res.ok_bind, Close.asValue_toSVal]
      exact Sim.trans (hW) (Sim.of_eq hw)
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨_, w', _, hs', hf⟩ := save_through qs (f :: t) hu
      obtain ⟨e, he⟩ := save_cons_asValue hs'
      refine Sim.halt (by simp only [saveLeaf, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      simp only [hf, Res.ok_bind, he, ne_eq, reduceCtorEq, not_false_eq_true, implies_true]
    | below k =>
      obtain ⟨f, t, rfl, -⟩ := hr
      refine Sim.halt (by simp only [saveLeaf, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      rw [SVal.findLive_append, findLive_saveLive_same hu]
      cases wv <;> simp only [Close.toSVal_int, Res.ok_bind, find_prim_cons, Res.error_bind,
          ne_eq, reduceCtorEq, not_false_eq_true, implies_true, Close.toSVal_bool]
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihR hv hq

theorem del_readU_sim {σ : State} {s : LStor} {P Q : LPath} {u : SVal} {qs : List Seg}
    (hu : (LStor.del s P).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihR : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    Sim (((LStor.del s P).readU Q).eval σ) (u.findLive qs >>= SVal.asValue) := by
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    rw [LStor.readU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      simp only [delLeaf, LTerm.eval, findLive_saveLive_same hu, Res.ok_bind, asValue_defaultOf]
      have h₁ := ihR hv hq
      rw [hc, Res.ok_bind] at h₁
      exact Sim.bind h₁ fun _ => Sim.refl _
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨_, w', _, hs', hf⟩ := save_through qs (f :: t) hu
      obtain ⟨e, he⟩ := save_cons_asValue hs'
      refine Sim.halt (by simp only [delLeaf, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      simp only [hf, Res.ok_bind, he, ne_eq, reduceCtorEq, not_false_eq_true, implies_true]
    | below rest =>
      obtain ⟨f, t, rfl, hrest⟩ := hr
      simp only [delLeaf]
      have hEnd : Sim ((LTerm.zero (s.readU Q)).eval σ)
          (v.findLive (ps ++ f :: t) >>= fun w => w.defaultOf.asValue) := by
        simp only [LTerm.eval]
        refine (Sim.bind (ihR hv hq) (fun _ => Sim.refl _)).trans
          (Sim.of_eq ?_)
        rw [bind_assoc]; congr 1; funext w; rw [asValue_defaultOf]
      have h := delBelow_sim (v := v) (G := SVal.asValue)
        (fun sh q qs hq' => ihM sh q hv hq') (ihR hv hq) hEnd
        rest P.elim ps (f :: t) hp' hrest rfl
      rw [hc, Res.ok_bind] at h
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind]
      exact h
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihR hv hq

theorem save_hasU_sim {σ : State} {s : LStor} {P Q : LPath} {w : LTerm} {u : SVal} {qs : List Seg}
    (hu : (LStor.save s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihH : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true))) :
    Sim (((LStor.save s P w).hasU Q).eval σ) (u.findLive qs >>= fun _ => .ok (.bool true)) := by
    obtain ⟨wv, hw, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    rw [LStor.hasU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      simp only [saveHas, findLive_saveLive_same hu, Res.ok_bind, LTerm.eval]
      exact Sim.refl _
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨_, w', _, _, hf⟩ := save_through qs (f :: t) hu
      simp only [saveHas, hf, Res.ok_bind, LTerm.eval]
      exact Sim.refl _
    | below k =>
      obtain ⟨f, t, rfl, -⟩ := hr
      refine Sim.halt (by simp only [saveHas, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      rw [SVal.findLive_append, findLive_saveLive_same hu]
      cases wv <;> simp only [Close.toSVal_int, Res.ok_bind, find_prim_cons, Res.error_bind,
          ne_eq, reduceCtorEq, not_false_eq_true, implies_true, Close.toSVal_bool]
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihH hv hq

theorem del_hasU_sim {σ : State} {s : LStor} {P Q : LPath} {u : SVal} {qs : List Seg}
    (hu : (LStor.del s P).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihH : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true)))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    Sim (((LStor.del s P).hasU Q).eval σ) (u.findLive qs >>= fun _ => .ok (.bool true)) := by
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    rw [LStor.hasU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      simp only [delHas, findLive_saveLive_same hu, Res.ok_bind, LTerm.eval]
      exact Sim.refl _
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨_, w', _, _, hf⟩ := save_through qs (f :: t) hu
      simp only [delHas, hf, Res.ok_bind, LTerm.eval]
      exact Sim.refl _
    | below rest =>
      obtain ⟨f, t, rfl, hrest⟩ := hr
      simp only [delHas]
      have h := delBelow_sim (v := v) (G := fun _ => .ok (.bool true))
        (fun sh q qs hq' => ihM sh q hv hq') (ihH hv hq)
        (ihH hv hq) rest P.elim ps (f :: t) hp' hrest rfl
      rw [hc, Res.ok_bind] at h
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind]
      exact h
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihH hv hq

theorem save_mapU_sim {σ : State} {s : LStor} {P Q : LPath} {w : LTerm} {u : SVal} {qs : List Seg} {sh : KShape}
    (hu : (LStor.save s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    Sim (((LStor.save s P w).mapU sh Q).eval σ) (u.findLive qs >>= sh.test) := by
    obtain ⟨wv, hw, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    rw [LStor.mapU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      refine Sim.halt (by simp only [saveMap, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      simp only [findLive_saveLive_same hu, Res.ok_bind]
      cases wv <;> cases sh <;> simp only [KShape.test, kmapF, isMapV, Value.toSVal,
          Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true, implies_true,
              isFixV]
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu
      simp only [saveMap, hf, Res.ok_bind, save_cons_kmapF hs']
      have := ihM sh Q hv hq
      rw [hw₀, Res.ok_bind] at this
      exact this
    | below rest =>
      obtain ⟨f, t, rfl, -⟩ := hr
      refine Sim.halt (by simp only [saveMap, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      rw [SVal.findLive_append, findLive_saveLive_same hu]
      cases wv <;> simp only [Close.toSVal_int, Res.ok_bind, find_prim_cons, Res.error_bind,
          ne_eq, reduceCtorEq, not_false_eq_true, implies_true, Close.toSVal_bool]
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihM sh Q hv hq

theorem del_mapU_sim {σ : State} {s : LStor} {P Q : LPath} {u : SVal} {qs : List Seg} {sh : KShape}
    (hu : (LStor.del s P).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    Sim (((LStor.del s P).mapU sh Q).eval σ) (u.findLive qs >>= sh.test) := by
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    rw [LStor.mapU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      simp only [delMap, findLive_saveLive_same hu, Res.ok_bind, KShape.test_defaultOf]
      have := ihM sh Q hv hq
      rw [hc, Res.ok_bind] at this
      exact this
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu
      simp only [delMap, hf, Res.ok_bind, save_cons_kmapF hs']
      have := ihM sh Q hv hq
      rw [hw₀, Res.ok_bind] at this
      exact this
    | below rest =>
      obtain ⟨f, t, rfl, hrest⟩ := hr
      simp only [delMap]
      have hEnd : Sim ((s.mapU sh Q).eval σ)
          (v.findLive (ps ++ f :: t) >>= fun w => sh.test w.defaultOf) := by
        simp only [KShape.test_defaultOf]; exact ihM sh Q hv hq
      have h := delBelow_sim (v := v) (G := sh.test)
        (fun sh' q qs hq' => ihM sh' q hv hq') (ihM sh Q hv hq)
        hEnd rest P.elim ps (f :: t) hp' hrest rfl
      rw [hc, Res.ok_bind] at h
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind]
      exact h
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihM sh Q hv hq

theorem save_lenU_sim {σ : State} {s : LStor} {P Q : LPath} {w : LTerm} {u : SVal} {qs : List Seg}
    (hu : (LStor.save s P w).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihL : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen)) :
    Sim (((LStor.save s P w).lenU Q).eval σ) (u.findLive qs >>= Close.arrLen) := by
    obtain ⟨wv, hw, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    rw [LStor.lenU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      refine Sim.halt (by simp only [saveMap, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      simp only [findLive_saveLive_same hu, Res.ok_bind]
      cases wv <;> simp only [Close.arrLen, Value.toSVal, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu
      simp only [saveMap, hf, Res.ok_bind, save_cons_arrLen hs']
      have := ihL hv hq
      rw [hw₀, Res.ok_bind] at this
      exact this
    | below rest =>
      obtain ⟨f, t, rfl, -⟩ := hr
      refine Sim.halt (by simp only [saveMap, LTerm.eval, ne_eq, reduceCtorEq, not_false_eq_true,
          implies_true]) ?_
      rw [SVal.findLive_append, findLive_saveLive_same hu]
      cases wv <;> simp only [Close.toSVal_int, Res.ok_bind, find_prim_cons, Res.error_bind,
          ne_eq, reduceCtorEq, not_false_eq_true, implies_true, Close.toSVal_bool]
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihL hv hq

theorem del_lenU_sim {σ : State} {s : LStor} {P Q : LPath} {u : SVal} {qs : List Seg}
    (hu : (LStor.del s P).eval σ = .ok u) (hq : Q.eval σ = .ok qs)
    (hP : Sim (P.elim.eval σ) (P.eval σ))
    (ihL : ∀ {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen))
    (ihM : ∀ (sh : KShape) (Q : LPath) {v qs}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)) :
    Sim (((LStor.del s P).lenU Q).eval σ) (u.findLive qs >>= Close.arrLen) := by
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (hP ps).2 hp
    have hEnd := lenEnd_sim (ihL hv hq) (ihM .fixed Q hv hq)
    rw [LStor.lenU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      simp only [delLen, findLive_saveLive_same hu, Res.ok_bind]
      rw [hc, Res.ok_bind] at hEnd
      exact hEnd
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu
      simp only [delLen, hf, Res.ok_bind, save_cons_arrLen hs']
      have := ihL hv hq
      rw [hw₀, Res.ok_bind] at this
      exact this
    | below rest =>
      obtain ⟨f, t, rfl, hrest⟩ := hr
      simp only [delLen]
      have h := delBelow_sim (v := v) (G := Close.arrLen)
        (fun sh' q qs hq' => ihM sh' q hv hq') (ihL hv hq)
        hEnd rest P.elim ps (f :: t) hp' hrest rfl
      rw [hc, Res.ok_bind] at h
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind]
      exact h
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact ihL hv hq

mutual

/-- **Eliminating the reads of writes keeps what a term returns.**

Example: after `balances[k] = 5; balances[j] = 6;`, the read of
`balances[k]` becomes `j == k ? 6 : (k == k ? 5 : balances[k])`, guarded by
the two writes succeeding; in every state it returns what the read does. -/
theorem LTerm.elim_sim (σ : State) : (t : LTerm) → Sim (t.elim.eval σ) (t.eval σ)
  | .lit _ => Sim.refl _
  | .var _ => Sim.refl _
  | .err => Sim.refl _
  | .env _ => Sim.refl _
  | .findP _ q => Sim.bind (Sim.refl _) fun _ => Sim.bind (LPath.elim_sim σ q) fun _ => Sim.refl _
  | .binop _ _ a b =>
    Sim.bind (LTerm.elim_sim σ a) fun _ => evalBinop_sim (LTerm.elim_sim σ b)
  | .unop _ _ a => Sim.bind (LTerm.elim_sim σ a) fun _ => Sim.refl _
  | .ite c a b =>
    Sim.bind (LTerm.elim_sim σ c) fun _ => pickBranch_sim (LTerm.elim_sim σ a) (LTerm.elim_sim σ b)
  | .find s q => guard_sim (LStor.okE_sim σ s) (LPath.elim_sim σ q)
      fun _ _ hv hq => LStor.readU_sim σ s q.elim hv hq
  | .has s q => guard_sim (LStor.okE_sim σ s) (LPath.elim_sim σ q)
      fun _ _ hv hq => LStor.hasU_sim σ s q.elim hv hq
  | .kmap sh s q => guard_sim (LStor.okE_sim σ s) (LPath.elim_sim σ q)
      fun _ _ hv hq => LStor.mapU_sim σ s sh q.elim hv hq
  | .len s q => guard_sim (LStor.okE_sim σ s) (LPath.elim_sim σ q)
      fun _ _ hv hq => LStor.lenU_sim σ s q.elim hv hq
  | .sok s => LStor.okE_sim σ s
  | .pok q => Sim.bind (LPath.elim_sim σ q) fun _ => Sim.refl _
  | .seq d a => Sim.bind (LTerm.elim_sim σ d) fun _ => LTerm.elim_sim σ a
  | .orElse a b => Sim.orElse (LTerm.elim_sim σ a) (LTerm.elim_sim σ b)
  | .kite a b t e =>
    Sim.bind (Sim.bind (LTerm.elim_sim σ a) fun _ => Sim.refl _) fun i =>
      Sim.bind (Sim.bind (LTerm.elim_sim σ b) fun _ => Sim.refl _) fun j => by
        by_cases h : i = j
        · simp only [h, if_true]; exact LTerm.elim_sim σ t
        · simp only [h, if_false]; exact LTerm.elim_sim σ e
  | .zero a => Sim.bind (LTerm.elim_sim σ a) fun _ => Sim.refl _
  | .cpok _ _ => Sim.refl _
termination_by structural x => x

/-- Eliminating keeps the path a path term names: `people[balances[a]]` after
`balances[a] = 5;` names `people[5]`. -/
theorem LPath.elim_sim (σ : State) : (q : LPath) → Sim (q.elim.eval σ) (q.eval σ)
  | .root _ => Sim.refl _
  | .field q _ => Sim.bind (LPath.elim_sim σ q) fun _ => Sim.refl _
  | .at q k => Sim.bind (LPath.elim_sim σ q) fun _ =>
      Sim.bind (Sim.bind (LTerm.elim_sim σ k) fun _ => Sim.refl _) fun _ => Sim.refl _
termination_by structural x => x

/-- The guard of a storage returns exactly when its writes do. -/
theorem LStor.okE_sim (σ : State) :
    (s : LStor) → Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true))
  | .init => Sim.refl _
  | .save s q w =>
    save_okE_sim (LStor.okE_sim σ s) (LTerm.elim_sim σ w) (LPath.elim_sim σ q) (fun hv hp => LStor.hasU_sim σ s q.elim hv hp)
  | .del s q =>
    del_okE_sim (LStor.okE_sim σ s) (LPath.elim_sim σ q) (fun hv hp => LStor.hasU_sim σ s q.elim hv hp)

  | .arr _ s P w => arr_okE_sim (LStor.okE_sim σ s) (LTerm.elim_sim σ w) (LPath.elim_sim σ P)
      fun hv hp => LStor.lenU_sim σ s P.elim hv hp
  | .copy s P src SQ => copy_okE_sim (LStor.okE_sim σ s) (LStor.okE_sim σ src) (LPath.elim_sim σ P)
      (LPath.elim_sim σ SQ) (fun hv hp => LStor.hasU_sim σ s P.elim hv hp)
      (fun hv hp => LStor.hasU_sim σ src SQ.elim hv hp)
  | .view _ _ => Sim.refl _
termination_by structural x => x

/-- **What a read after writes returns**, peeled one write at a time. -/
theorem LStor.readU_sim (σ : State) : (s : LStor) → ∀ (Q : LPath) {v : SVal} {qs : List Seg},
    s.eval σ = .ok v → Q.eval σ = .ok qs → Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue)
  | .init, Q, v, qs, hv, hq => by
    cases hv
    simp only [LStor.readU, LTerm.eval, LStor.eval, hq, Res.ok_bind]
    exact Sim.refl _
  | .save s P w, Q, u, qs, hu, hq =>
    save_readU_sim hu hq (LPath.elim_sim σ P) (LTerm.elim_sim σ w) (fun hv hq => LStor.readU_sim σ s Q hv hq)
  | .del s P, Q, u, qs, hu, hq =>
    del_readU_sim hu hq (LPath.elim_sim σ P) (fun hv hq => LStor.readU_sim σ s Q hv hq) (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)

  | .arr _ s P w, Q, _, _, hu, hq => arr_readU_sim hu hq (LPath.elim_sim σ P) (LTerm.elim_sim σ w)
      (fun hv hq => LStor.readU_sim σ s Q hv hq) (fun hv hp => LStor.lenU_sim σ s P.elim hv hp)
      (fun rest opq _ _ _ _ _ _ _ hv hp hn hr hopq =>
        LStor.slotU_sim σ s P.elim rest opq hv hp hn hr hopq)
  | .copy s P src SQ, Q, _, _, hu, hq => copy_readU_sim hu hq (LPath.elim_sim σ P)
      (LPath.elim_sim σ SQ) (fun hv hq => LStor.readU_sim σ s Q hv hq)
      (fun Q' _ _ hv hq => LStor.readU_sim σ src Q' hv hq)
      (fun Q' _ _ hv hq => LStor.mapU_sim σ src .map Q' hv hq)
  | .view _ _, Q, v, qs, hv, hq => by
    simp only [LStor.readU, LTerm.eval, hv, hq, Res.ok_bind]
    exact Sim.refl _
termination_by structural x => x

/-- **What the slot a `push()` recycles holds.** -/
theorem LStor.slotU_sim (σ : State) : (s : LStor) → ∀ (P : LPath) (rest : List SSeg) (opq : LTerm)
    {v : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool} {R : RefTy} {r : List Seg},
    s.eval σ = .ok v → P.eval σ = .ok ps → v.findLive ps = .ok (.array es sh fx) →
    segsEval σ rest = .ok r →
    Sim (opq.eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue) →
    Sim ((s.slotU P rest opq).eval σ) ((pushSlot (.ref R) sh).1.findLive r >>= SVal.asValue)
  | .arr (.pop _) s P' _ => fun P _ _ _ _ _ _ _ _ _ hv hp hn hr hopq =>
    pop_slotU_sim hv (LPath.elim_sim σ P') hp hn hr hopq
      (fun Q _ _ hv hq => LStor.readU_sim σ s Q hv hq)
      (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)
      (fun hv hq => LStor.lenU_sim σ s P hv hq)
  | .del s P' => fun P _ _ _ _ _ _ _ _ _ hv hp hn hr hopq =>
    del_slotU_sim hv (LPath.elim_sim σ P') hp hn hr hopq
      (fun Q _ _ hv hq => LStor.readU_sim σ s Q hv hq)
      (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)
      (fun hv hq => LStor.lenU_sim σ s P hv hq)
  | .init => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotU]; exact hopq
  | .save .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotU]; exact hopq
  | .arr .push .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotU]; exact hopq
  | .arr (.slot _) .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotU]; exact hopq
  | .copy .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotU]; exact hopq
  | .view .. => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hopq => by rw [LStor.slotU]; exact hopq
termination_by structural x => x

/-- **Whether a location is there after writes**, peeled one write at a time. -/
theorem LStor.hasU_sim (σ : State) : (s : LStor) → ∀ (Q : LPath) {v : SVal} {qs : List Seg},
    s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true))
  | .init, Q, v, qs, hv, hq => by
    cases hv
    simp only [LStor.hasU, LTerm.eval, LStor.eval, hq, Res.ok_bind]
    exact Sim.refl _
  | .save s P w, Q, u, qs, hu, hq =>
    save_hasU_sim hu hq (LPath.elim_sim σ P) (fun hv hq => LStor.hasU_sim σ s Q hv hq)
  | .del s P, Q, u, qs, hu, hq =>
    del_hasU_sim hu hq (LPath.elim_sim σ P) (fun hv hq => LStor.hasU_sim σ s Q hv hq) (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)

  | .arr _ s P _, Q, _, _, hu, hq => arr_hasU_sim hu hq (LPath.elim_sim σ P)
      (fun hv hq => LStor.hasU_sim σ s Q hv hq) (fun hv hp => LStor.lenU_sim σ s P.elim hv hp)
  | .copy s P src SQ, Q, _, _, hu, hq => copy_hasU_sim hu hq (LPath.elim_sim σ P)
      (LPath.elim_sim σ SQ) (fun hv hq => LStor.hasU_sim σ s Q hv hq)
      (fun Q' _ _ hv hq => LStor.hasU_sim σ src Q' hv hq)
      (fun Q' _ _ hv hq => LStor.mapU_sim σ src .map Q' hv hq)
  | .view _ _, Q, v, qs, hv, hq => by
    simp only [LStor.hasU, LTerm.eval, hv, hq, Res.ok_bind]
    exact Sim.refl _
termination_by structural x => x

/-- **Whether a mapping is there after writes**, peeled one write at a time. -/
theorem LStor.mapU_sim (σ : State) : (s : LStor) → ∀ (sh : KShape) (Q : LPath) {v : SVal}
    {qs : List Seg}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)
  | .init, sh, Q, v, qs, hv, hq => by
    cases hv
    simp only [LStor.mapU, LTerm.eval, LStor.eval, hq, Res.ok_bind]
    exact Sim.refl _
  | .save s P w, sh, Q, u, qs, hu, hq =>
    save_mapU_sim hu hq (LPath.elim_sim σ P) (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)
  | .del s P, sh, Q, u, qs, hu, hq =>
    del_mapU_sim hu hq (LPath.elim_sim σ P) (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)

  | .arr _ s P _, sh, Q, _, _, hu, hq => arr_mapU_sim hu hq (LPath.elim_sim σ P)
      (fun hv hq => LStor.mapU_sim σ s sh Q hv hq) (fun hv hp => LStor.lenU_sim σ s P.elim hv hp)
  | .copy s P src SQ, sh, Q, _, _, hu, hq => copy_mapU_sim hu hq (LPath.elim_sim σ P)
      (LPath.elim_sim σ SQ) (fun hv hq => LStor.mapU_sim σ s sh Q hv hq)
      (fun Q' _ _ hv hq => LStor.mapU_sim σ src sh Q' hv hq)
      (fun Q' _ _ hv hq => LStor.mapU_sim σ src .map Q' hv hq)
  | .view _ _, sh, Q, v, qs, hv, hq => by
    simp only [LStor.mapU, LTerm.eval, hv, hq, Res.ok_bind]
    exact Sim.refl _
termination_by structural x => x

/-- **The length of an array after writes**, peeled one write at a time. -/
theorem LStor.lenU_sim (σ : State) : (s : LStor) → ∀ (Q : LPath) {v : SVal} {qs : List Seg},
    s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen)
  | .init, Q, v, qs, hv, hq => by
    cases hv
    simp only [LStor.lenU, LTerm.eval, LStor.eval, hq, Res.ok_bind]
    exact Sim.refl _
  | .save s P w, Q, u, qs, hu, hq =>
    save_lenU_sim hu hq (LPath.elim_sim σ P) (fun hv hq => LStor.lenU_sim σ s Q hv hq)
  | .del s P, Q, u, qs, hu, hq =>
    del_lenU_sim hu hq (LPath.elim_sim σ P) (fun hv hq => LStor.lenU_sim σ s Q hv hq) (fun sh Q _ _ hv hq => LStor.mapU_sim σ s sh Q hv hq)
  | .arr _ s P _, Q, _, _, hu, hq => arr_lenU_sim hu hq (LPath.elim_sim σ P)
      (fun hv hq => LStor.lenU_sim σ s Q hv hq) (fun hv hp => LStor.lenU_sim σ s P.elim hv hp)
  | .copy s P src SQ, Q, _, _, hu, hq => copy_lenU_sim hu hq (LPath.elim_sim σ P)
      (LPath.elim_sim σ SQ) (fun hv hq => LStor.lenU_sim σ s Q hv hq)
      (fun Q' _ _ hv hq => LStor.lenU_sim σ src Q' hv hq)
      (fun Q' _ _ hv hq => LStor.mapU_sim σ src .map Q' hv hq)
  | .view _ _, Q, v, qs, hv, hq => by
    simp only [LStor.lenU, LTerm.eval, hv, hq, Res.ok_bind]
    exact Sim.refl _
termination_by structural x => x
end

/-- Eliminating keeps the meaning of a formula: an equation holds when both
sides return and agree, and eliminating keeps what they return. -/
theorem LFml.elim_holds (σ : State) : (φ : LFml) → (φ.elim.holds σ ↔ φ.holds σ)
  | .tt => Iff.rfl
  | .eq a b => by
    have ha := LTerm.elim_sim σ a
    have hb := LTerm.elim_sim σ b
    simp only [LFml.elim, LFml.holds]
    cases h₁ : a.eval σ with
    | error e =>
      have : ∀ x, a.elim.eval σ ≠ .ok x := fun x hx => by simp only [(ha x).1 hx,
          reduceCtorEq] at h₁
      cases h₂ : a.elim.eval σ with
      | error => simp only
      | ok x => exact absurd h₂ (this x)
    | ok x =>
      rw [(ha x).2 h₁]
      cases h₃ : b.eval σ with
      | error e =>
        have : ∀ y, b.elim.eval σ ≠ .ok y := fun y hy => by simp only [(hb y).1 hy,
            reduceCtorEq] at h₃
        cases h₄ : b.elim.eval σ with
        | error => simp only
        | ok y => exact absurd h₄ (this y)
      | ok y => rw [(hb y).2 h₃]
  | .not φ => by simp only [LFml.elim, LFml.holds, LFml.elim_holds σ φ]
  | .and φ ψ => by simp only [LFml.elim, LFml.holds, LFml.elim_holds σ φ, LFml.elim_holds σ ψ]
  | .imp φ ψ => by simp only [LFml.elim, LFml.holds, LFml.elim_holds σ φ, LFml.elim_holds σ ψ]
  | .all x p φ => by
    simp only [LFml.elim, LFml.holds]
    exact forall_congr' fun v => imp_congr_right fun _ => LFml.elim_holds _ φ

/-! ## The reduction -/

/-- What `sol_decide` proves of `φ`: its updates pushed in, the reads of
writes eliminated.  What is left reads the initial state only: its locals,
and the words and locations of its storage. -/
def _root_.Solidity.Fml.reduce (φ : Fml C) : LFml := (φ.toL Sym.empty).elim

/-- **`⊨ φ` is exactly `φ.reduce` in every state**, for every `φ` in the
fragment: nothing valid is lost, nothing invalid is gained.

Example: what symbolic execution leaves of
`[ balances[k] = 5; balances[j] = 6; uint y = balances[k]; ] (k == j → y == 6)`
is valid exactly when its reduction, a statement about `k`, `j` and whether
`balances[k]` and `balances[j]` are locations, holds in every state. -/
theorem _root_.Solidity.Fml.valid_iff_reduce (φ : Fml C) (hf : φ.inL Sym.empty = true) :
    (⊨ φ) ↔ ∀ σ, φ.reduce.holds σ := by
  rw [Fml.valid_iff_toL φ hf]
  exact forall_congr' fun σ => (LFml.elim_holds σ _).symm

/-! ### Unfolding the reduced formula

The reduced formula reads the initial state only, so it unfolds to a
statement about `σ.getEnv x` and the storage tree `SVal.struct σ.storage`,
which stay atoms.  The equations below state it in `sol_close`'s weakest
preconditions, so that `close_rw` takes it from there. -/

theorem LFml.holds_tt (σ : State) : LFml.tt.holds σ ↔ True := Iff.rfl
/-- `k != j` is `¬ k = j`. -/
theorem LFml.holds_not (σ : State) (φ : LFml) : (LFml.not φ).holds σ ↔ ¬ φ.holds σ := Iff.rfl
/-- `y == 0 && z == 30`. -/
theorem LFml.holds_and (σ : State) (φ ψ : LFml) :
    (LFml.and φ ψ).holds σ ↔ φ.holds σ ∧ ψ.holds σ := Iff.rfl
/-- `k == j → y == 6`. -/
theorem LFml.holds_imp (σ : State) (φ ψ : LFml) :
    (LFml.imp φ ψ).holds σ ↔ (φ.holds σ → ψ.holds σ) := Iff.rfl

/-- `y == 6`: both sides return, and agree. -/
theorem LFml.holds_eq (σ : State) (a b : LTerm) : (LFml.eq a b).holds σ ↔
    Modality.diamond.wp (a.eval σ) fun x => Modality.diamond.wp (b.eval σ) fun y => x = y := by
  simp only [LFml.holds]
  cases a.eval σ <;> cases b.eval σ <;> simp only [Modality.wp, Modality.onHalt]

/-- `delete` of a `uint` leaves `0`. -/
theorem zeroV_int (v : Int) : zeroV (.int v) = .int 0 := rfl
/-- `delete` of a `bool` leaves `false`. -/
theorem zeroV_bool (b : Bool) : zeroV (.bool b) = .bool false := rfl

/-! ## The tactic -/

open Lean Elab Tactic Meta in
/-- Compute `φ.reduce` in a goal `∀ σ, (Fml.reduce φ).holds σ`: the formula
is closed after `sol_symex`, so it is run as compiled code and quoted back,
and the kernel checks the result (`replaceTargetDefEq`), as mini-solkey's
`reduceGoal` does. -/
def reduceGoal (g : MVarId) : MetaM MVarId := do
  let ty ← instantiateMVars (← g.getType)
  let .forallE n d b bi := ty | throwError "sol_decide: expected `∀ σ, …`"
  let_expr LFml.holds _ r := b | throwError "sol_decide: expected `LFml.holds σ …`"
  let r' ← if r.hasFVar || r.hasMVar || r.hasLooseBVars then
      withTransparency .all <| Meta.reduce r (skipTypes := true) (skipProofs := true)
    else
      pure (toExpr (← unsafe evalExpr LFml (mkConst ``LFml) r))
  g.replaceTargetDefEq (.forallE n d (mkApp2 (mkConst ``LFml.holds) (.bvar 0) r') bi)

open Lean Elab Tactic in
/-- Replace `Fml.reduce φ` by the formula it computes to. -/
elab "sol_reduce" : tactic => do replaceMainGoal [← reduceGoal (← getMainGoal)]


/-- The free locals of a formula. -/
def LFml.vars : LFml → List Var
  | .tt => []
  | .eq a b => a.vars ++ b.vars
  | .not φ => φ.vars
  | .and φ ψ | .imp φ ψ => φ.vars ++ ψ.vars
  | .all _ _ φ => φ.vars

/-- A local read as a value halts, is an integer, or is a boolean. -/
theorem value_cases (r : Res Value) :
    (∃ e, r = .error e) ∨ (∃ i, r = .ok (.int i)) ∨ ∃ b, r = .ok (.bool b) := by
  rcases r with e | (i | b)
  · exact .inl ⟨e, rfl⟩
  · exact .inr (.inl ⟨i, rfl⟩)
  · exact .inr (.inr ⟨b, rfl⟩)

/-! The equations of `LTerm.eval` but the local's: a local is split on
first (`sol_decide_split`), so that a key is an integer before the key
tests are unfolded. -/

/-- `10` is `10`. -/
theorem LTerm.eval_lit (σ : State) (v : Value) : (LTerm.lit v).eval σ = .ok v := rfl
/-- `x + 1`: `x`, then the operator. -/
theorem LTerm.eval_binop (σ : State) (op : BinOp) (p : PrimTy) (a b : LTerm) :
    (LTerm.binop op p a b).eval σ = a.eval σ >>= fun x => evalBinop op p x (b.eval σ) := rfl
/-- `!flag`: the operand, then the operator. -/
theorem LTerm.eval_unop (σ : State) (op : UnOp) (p : PrimTy) (a : LTerm) :
    (LTerm.unop op p a).eval σ = a.eval σ >>= fun x => applyUnOp op x >>= unopCheck op p := rfl
/-- `c ? a : b`: the condition, then the branch. -/
theorem LTerm.eval_ite (σ : State) (c a b : LTerm) :
    (LTerm.ite c a b).eval σ = c.eval σ >>= fun cv => pickBranch cv (a.eval σ) (b.eval σ) := rfl
/-- `balances[k]`: the storage, the path, the word there. -/
theorem LTerm.eval_find (σ : State) (s : LStor) (q : LPath) : (LTerm.find s q).eval σ =
    s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= SVal.asValue := rfl
/-- `balances[k]` is a location. -/
theorem LTerm.eval_has (σ : State) (s : LStor) (q : LPath) : (LTerm.has s q).eval σ =
    s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= fun _ => .ok (.bool true) := rfl
/-- `ledger.balances` is a mapping. -/
theorem LTerm.eval_kmap (σ : State) (sh : KShape) (s : LStor) (q : LPath) :
    (LTerm.kmap sh s q).eval σ =
      s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= sh.test := rfl
/-- `values.length`. -/
theorem LTerm.eval_len (σ : State) (s : LStor) (q : LPath) : (LTerm.len s q).eval σ =
    s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= Close.arrLen := rfl
/-- `a`, or `b` where `a` halts. -/
theorem LTerm.eval_orElse (σ : State) (a b : LTerm) :
    (LTerm.orElse a b).eval σ = orElseR (a.eval σ) (b.eval σ) := rfl
/-- `balances[k] = 5;` succeeds. -/
theorem LTerm.eval_sok (σ : State) (s : LStor) :
    (LTerm.sok s).eval σ = s.eval σ >>= fun _ => .ok (.bool true) := rfl
/-- The key `k` of `balances[k]` is an integer. -/
theorem LTerm.eval_pok (σ : State) (q : LPath) :
    (LTerm.pok q).eval σ = q.eval σ >>= fun _ => .ok (.bool true) := rfl
/-- The guard, then the read. -/
theorem LTerm.eval_seq (σ : State) (d a : LTerm) :
    (LTerm.seq d a).eval σ = d.eval σ >>= fun _ => a.eval σ := rfl
/-- `k == j ? 6 : 5`, the keys compared as integers. -/
theorem LTerm.eval_kite (σ : State) (a b t e : LTerm) : (LTerm.kite a b t e).eval σ =
    (a.eval σ >>= Value.asInt) >>= fun i => (b.eval σ >>= Value.asInt) >>= fun j =>
      if i = j then t.eval σ else e.eval σ := rfl
/-- `delete alice.age;` then `alice.age`: the default of the old word. -/
theorem LTerm.eval_zero (σ : State) (a : LTerm) :
    (LTerm.zero a).eval σ = a.eval σ >>= fun v => .ok (zeroV v) := rfl
/-- A read above a write: `alice` after `alice.age = 3;` is no word. -/
theorem LTerm.eval_err (σ : State) : LTerm.err.eval σ = .error .stuck := rfl
theorem LTerm.eval_env (σ : State) (k : EnvKey) :
    (LTerm.env k).eval σ = .ok (.int (σ.envVal k)) := rfl
theorem LTerm.eval_findP (σ : State) (s : LStor) (q : LPath) : (LTerm.findP s q).eval σ =
    s.eval σ >>= fun v => q.eval σ >>= fun qs => v.find qs >>= SVal.asValue := rfl

open Lean Elab Tactic Meta in
/-- Split on every local of the reduced formula: it halts, is an integer,
or is a boolean.  Afterwards every key is a known integer or halts, and the
key tests unfold to `if i = j`. -/
elab "sol_decide_split" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr LFml.holds σ r := ty | throwError "sol_decide: expected `LFml.holds σ …`"
  let xs ← unsafe evalExpr (List Var) (mkApp (mkConst ``List [levelZero]) (mkConst ``Var))
    (mkApp (mkConst ``LFml.vars) r)
  for x in xs.eraseDups do
    let t := mkApp2 (mkConst ``LTerm.eval) σ (mkApp (mkConst ``LTerm.var) (toExpr x))
    let tt ← Term.exprToSyntax t
    evalTactic (← `(tactic| all_goals
      rcases value_cases $tt with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩))

/-- A storage read halts, or is a word, a struct, an array of either kind, or
a mapping. -/
theorem sval_cases (r : Res SVal) :
    (∃ e, r = .error e) ∨ (∃ p, r = .ok (.prim p)) ∨ (∃ fs, r = .ok (.struct fs)) ∨
      (∃ es sh, r = .ok (.array es sh false)) ∨ (∃ es sh, r = .ok (.array es sh true)) ∨
      ∃ es d, r = .ok (.map es d) := by
  rcases r with e | ((p | fs | ⟨es, sh, _ | _⟩ | ⟨es, d⟩))
  · exact .inl ⟨e, rfl⟩
  · exact .inr (.inl ⟨p, rfl⟩)
  · exact .inr (.inr (.inl ⟨fs, rfl⟩))
  · exact .inr (.inr (.inr (.inl ⟨es, sh, rfl⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨es, sh, rfl⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨es, d, rfl⟩))))

open Lean Elab Tactic Meta in
/-- Split on the shape of every storage read a shape case makes: where a read
below a deleted location crosses a key, what it returns depends on whether the
location above the key is a mapping or a fixed-size array (`delBelow`, the
hypotheses with an `orElseR`), and a case on the read's result settles the
shape tests. -/
elab "sol_decide_reads" : tactic => withMainContext do
  let mut reads : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    -- only the reads a shape case (`orElseR`, `delBelow`) depends on
    unless ty.find? (·.isConstOf ``orElseR) |>.isSome do continue
    let found : Array Expr ← (StateT.run (s := #[]) do
      ty.forEachWhere (fun e => e.isAppOfArity ``SVal.findLive 2 && !e.hasLooseBVars)
        fun e => (modify (·.push e) : StateT (Array Expr) TacticM Unit)) <&> (·.2)
    for e in found do
      unless reads.contains e do reads := reads.push e
  for e in reads do
    let t ← Term.exprToSyntax e
    evalTactic (← `(tactic| all_goals
      rcases sval_cases $t with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩))

attribute [decide_eval] LFml.holds_tt LFml.holds_not LFml.holds_and LFml.holds_imp
  LFml.holds_eq LTerm.eval_lit LTerm.eval_binop LTerm.eval_unop LTerm.eval_ite LTerm.eval_find
  LTerm.eval_has LTerm.eval_kmap LTerm.eval_len LTerm.eval_sok LTerm.eval_pok LTerm.eval_seq
  LTerm.eval_kite LTerm.eval_zero LTerm.eval_err LTerm.eval_env LTerm.eval_findP
  LTerm.eval_orElse LPath.eval
  LStor.eval State.envVal
  zeroV_int zeroV_bool KShape.test kmapF isMapV isFixV orElseR_ok orElseR_error

/-- The first pass of `sol_decide` after the split: unfold the reduced
formula into `sol_close`'s weakest preconditions. -/
macro "sol_decide_unfold" : tactic => `(tactic|
  set_option linter.unusedSimpArgs false in
  simp only [decide_eval, close_rw, *])

/-- The second: every fact in scope for every other. -/
macro "sol_decide_facts" : tactic => `(tactic|
  simp_all (config := { maxSteps := 400000 }) only [decide_eval, close_rw])

/-- The finishing step without the constraints, on a goal `∀ σ, ψ.holds σ`
with `ψ` computed: split on the locals, unfold, and close with `simp`,
`omega` and `grind`, splitting on the shape of a read below a deleted
location where `delBelow` asks.  It does not know how two reads of the
initial storage constrain each other; `sol_decide` (`DecideComplete.lean`)
runs it where the reduction still writes through a member named `length`,
which the constraints do not cover. -/
macro "sol_decide_heuristic" : tactic => `(tactic| (
    intro σ
    sol_decide_split
    all_goals sol_decide_unfold
    all_goals (intros; subst_vars)
    all_goals try sol_decide_facts
    all_goals (try intros)
    -- a read below a deleted location through a key is a case on the
    -- location's shape (`delBelow`): its binds opened, it is a case split
    all_goals first | omega | grind | (sol_decide_reads <;> simp_all only [Res.ok_bind,
      Res.error_bind, KShape.test, kmapF, isMapV, isFixV, orElseR_ok, orElseR_error, if_true,
      if_false, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] <;> grind)))

end Decide

end Solidity
