import Solidity.Calculus.Close
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
(`values.length`, `LStor.lenU`); one write of a value
or one `delete` over `storage` per update; every alias bound by an update
and, through an index, used before the next write to the storage; a storage
variable bound to the storage (`old` of a specification, read as a snapshot:
`LTerm.findP`); a ledger entry or a payment (`transfer`'s), which no term of
the fragment reads; a quantifier over a local the updates before it do not
read (`LFml.all`, a specification's `\forall`).  Outside it: memory (`read`,
`write`, allocation, the copies `copySt`/`copyMem`), a copy between storage
locations (`alice = bob;`), `push`/`pop`, a read of the ledger (`net(a)`).  Of the gaps `Close.lean` lists, this closes the keys the
formula does not separate and the reads below a deleted struct; the memory
defaults and the distinct allocations stay open.
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
      simp [SVal.saveLive] at h
      subst updated
      simp
  | cons seg rest ih =>
      cases seg with
      | field name =>
          cases old <;> try { simp [SVal.saveLive] at h }
          rename_i fields
          cases hv : lookupBy name fields with
          | none => simp [SVal.saveLive, hv] at h
          | some old =>
              simp only [SVal.saveLive, hv] at h
              obtain ⟨child, hs, h⟩ := Res.bind_eq_ok.1 h
              cases h
              simp [SVal.findLive, lookupBy_setBy_self, ih hs]
      | «at» i =>
          cases old <;> try { simp [SVal.saveLive] at h }
          · rename_i elems shadow fx
            simp only [SVal.saveLive] at h
            split at h
            next hb =>
              obtain ⟨child, hs, h⟩ := Res.bind_eq_ok.1 h
              cases h
              simp [SVal.findLive, hb, ih hs]
            next hb => contradiction
          · rename_i entries dflt
            cases hv : lookupBy i entries with
            | none =>
                simp only [SVal.saveLive, hv] at h
                obtain ⟨child, hs, h⟩ := Res.bind_eq_ok.1 h
                cases h
                simp [SVal.findLive, lookupBy_setBy_self, ih hs]
            | some old =>
                simp only [SVal.saveLive, hv] at h
                obtain ⟨child, hs, h⟩ := Res.bind_eq_ok.1 h
                cases h
                simp [SVal.findLive, lookupBy_setBy_self, ih hs]

/-- **Frame, live**: a write leaves every path apart from it as it was. -/
theorem findLive_saveLive_diverge {new : SVal} :
    ∀ {p q : List Seg} {old upd : SVal}, Close.Diverge p q → old.saveLive p new = .ok upd →
      upd.findLive q = old.findLive q
  | [], _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => (Close.not_diverge_nil_right h).elim
  | a :: p, b :: q, old, upd, h, hs => by
    cases old with
    | prim v => cases a <;> simp [SVal.saveLive] at hs
    | struct fields =>
      cases a with
      | «at» i => simp [SVal.saveLive] at hs
      | field n =>
        simp only [SVal.saveLive] at hs
        split at hs
        · rename_i old' hl
          obtain ⟨u, hu, hs⟩ := Res.bind_eq_ok.1 hs
          cases hs
          cases b with
          | «at» j => simp [SVal.findLive]
          | field m =>
            by_cases hnm : m = n
            · subst hnm
              have hd : Close.Diverge p q := by simpa using h
              simp [SVal.findLive, hl, findLive_saveLive_diverge hd hu]
            · simp [SVal.findLive, lookupBy_setBy_ne hnm]
        · simp at hs
    | array elems shadow fx =>
      cases a with
      | field n => simp [SVal.saveLive] at hs
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
            · subst hm; cases fx <;> simp [SVal.findLive]
            · simp [SVal.findLive]
          | «at» j =>
            by_cases hij : j = i
            · subst hij
              have hd : Close.Diverge p q := by simpa using h
              simp [SVal.findLive, hi, findLive_saveLive_diverge hd hu]
            · by_cases hj : 0 ≤ j ∧ j.toNat < elems.length
              · have hne : i.toNat ≠ j.toNat := by omega
                simp [SVal.findLive, hj, List.getElem_set_ne hne]
              · simp [SVal.findLive, hj]
        · simp at hs
    | map entries dflt =>
      cases a with
      | field n => simp [SVal.saveLive] at hs
      | «at» i =>
        simp only [SVal.saveLive] at hs
        -- the slot written: the entry at `i`, or the default when there is none
        obtain ⟨old', hold, hfind⟩ : ∃ old' : SVal, (old'.saveLive p new >>= fun u =>
            Except.ok (SVal.map (setBy i u entries) dflt)) = Except.ok upd ∧
            (SVal.map entries dflt).findLive (.at i :: q) = old'.findLive q := by
          split at hs <;> rename_i hl <;> exact ⟨_, hs, by simp [SVal.findLive, hl]⟩
        obtain ⟨u, hu, hold⟩ := Res.bind_eq_ok.1 hold
        cases hold
        cases b with
        | field m => simp [SVal.findLive]
        | «at» j =>
          by_cases hij : j = i
          · subst hij
            have hd : Close.Diverge p q := by simpa using h
            simp [SVal.findLive] at hfind ⊢
            rw [hfind, findLive_saveLive_diverge hd hu]
          · simp [SVal.findLive, lookupBy_setBy_ne hij]

/-! ## The target language

A term here is read in the state the formula *starts* in: every update has
been pushed into it.  A storage is a stack of writes over that state's
storage (`LStor`), and the storage as a whole is one tree, the struct of its
roots (`SVal.struct σ.storage`), so that a root is the first segment of a
path and a write at a root is a write like any other. -/

/-- A shape the location above a key is tested for, below a `delete`: a
mapping keeps its entries (`delete` leaves it alone), a fixed-size array keeps
its elements' places (`delete` resets them in place). -/
inductive KShape where
  | map
  | fixed
  deriving Inhabited, Repr, DecidableEq, Lean.ToExpr

deriving instance Lean.ToExpr for EnvKey
deriving instance Lean.ToExpr for PrimTy

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
  deriving Inhabited, Repr, Lean.ToExpr

end

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
  | .find s q | .has s q | .kmap _ s q | .len s q | .findP s q => s.vars ++ q.vars
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
    have hy : y ≠ x := fun e => h (by simp [LTerm.vars, e])
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
  deriving Inhabited

/-- The updates so far: the names bound, newest first, and the storage. -/
structure Sym where
  env : List (Var × SymB)
  stor : LStor

/-- No update yet. -/
def Sym.empty : Sym := ⟨[], .init⟩

variable {C : Contract}

/-- A path whose key is not an integer: what an alias bound to a value
resolves to. -/
def LPath.stuck : LPath := .at (.root "") .err

/-- What `toL` gives at each sort: a value or a stored value is an `LTerm`, a
path an `LPath`, a storage an `LStor`; the memory sorts are outside. -/
@[reducible] def _root_.Solidity.Srt.LTy : Srt → Type
  | .val => LTerm
  | .path => LPath
  | .st => LStor
  | .sv => LTerm
  | .ident | .addr | .mem | .mv => Unit

/-- A constant with the updates `ρ` pushed in. -/
def _root_.Solidity.Op0.toL (ρ : Sym) : Op0 s → s.LTy
  | .lit v => .lit v
  | .env k => .env k
  | .root r => .root r
  | .storage => ρ.stor
  | .memory => ()

/-- A unary symbol over its argument's `toL`. -/
def _root_.Solidity.Op1.toL : Op1 a s → a.LTy → s.LTy
  | .unop op p, x => .unop op p x
  | .net, _ => .err
  | .netOf _, _ => .err
  | .delValue, _ => .err
  | .field f, x => .field x f
  | .next, _ => .stuck
  | .select _, _ => .init
  | .sval, x => x
  | .newArr _, _ => .err
  | .alloc _, _ => ()
  | .mfield _, _ => ()
  | .addM _, _ => ()
  | .mval, _ => ()
  | .ref, _ => ()

/-- A binary symbol over its arguments' `toL`. -/
def _root_.Solidity.Op2.toL : Op2 a b s → a.LTy → b.LTy → s.LTy
  | .binop op p, x, y => .binop op p x y
  | .find, x, y => .find x y
  | .len, x, y => .len x y
  | .read, _, _ => .err
  | .mlen, _, _ => .err
  | .at, x, y => .at x y
  | .nextIn, _, _ => .stuck
  | .delAt, x, y => .del x y
  | .pushSlot _, _, _ => .init
  | .pop, _, _ => .init
  | .shrink, _, _ => .init
  | .extend _, _, _ => .init
  | .sfind, _, _ => .err
  | .copyMem, _, _ => .err
  | .iread, _, _ => ()
  | .copy, _, _ => ()
  | .mat, _, _ => ()
  | .copySt, _, _ => ()

/-- A ternary symbol over its arguments' `toL`. -/
def _root_.Solidity.Op3.toL : Op3 a b c s → a.LTy → b.LTy → c.LTy → s.LTy
  | .ite, x, y, z => .ite x y z
  | .save, x, y, z => .save x y z
  | .push, _, _, _ => .init
  | .atIn, _, _, _ => .stuck
  | .write, _, _, _ => ()

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
    · simp at h
  · simp at h

/-- A term with the updates `ρ` pushed in: after `{ y := find(storage,
balances[k]) }`, `y` is that read; after `{ sp1 := alice.account }`,
`sp1.balance` is `alice.account.balance`; after `{ storage := save(storage,
balances[k], 5) }`, `storage` is that write. -/
def _root_.Solidity.Tm.toL (ρ : Sym) : Tm C s → s.LTy
  | .pvV x =>
    match lookupBy x ρ.env with
    | some (.val t) => t
    | some (.path _) | some .stale | some (.stor _) => .err
    | none => .var x
  | .pvP x =>
    match lookupBy x ρ.env with
    | some (.path q) => q
    | _ => .stuck
  | .pvS _ => .init
  | .pvI _ => ()
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

/-- The locals the updates so far read: a quantifier may bind none of them. -/
def Sym.vars (ρ : Sym) : List Var := ρ.stor.vars ++ ρ.env.flatMap fun b => b.2.vars

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
  | .lit _ | .env _ | .root _ | .storage => true
  | .memory => false

/-- A unary symbol in the fragment, its argument in it (`hb`). -/
def _root_.Solidity.Op1.inL : Op1 a s → Bool → Bool
  | .unop .., hb | .field _, hb | .sval, hb => hb
  | _, _ => false

/-- A binary symbol in the fragment, its arguments in it (`ha`, `hb`); a
read or a delete is of `storage` itself. -/
def _root_.Solidity.Op2.inL (ρ : Sym) : Op2 a b s → Tm C a → Bool → Bool → Bool
  | .binop .., _, ha, hb | .at, _, ha, hb => ha && hb
  | .find, s, _, hb => (s.isStorage || (s.storLocal? ρ).isSome) && hb
  | .len, s, _, hb | .delAt, s, _, hb => s.isStorage && hb
  | _, _, _, _ => false

/-- A ternary symbol in the fragment: a conditional, or a write over
`storage` itself. -/
def _root_.Solidity.Op3.inL : Op3 a b c s → Tm C a → Bool → Bool → Bool → Bool
  | .ite, _, hc, ha, hb => hc && ha && hb
  | .save, s, _, hp, hv => s.isStorage && hp && hv
  | _, _, _, _, _ => false

/-- The fragment: storage values and paths only, every alias bound by an
update.  A read is of the storage the updates left, `find(storage, p)`: its
path is checked against that storage, and read there.  A path's alias only
where an update bound it (`Person storage p = alice;` does), and to a path
with no index.  A storage: one write of a word, or one `delete`, over the
storage the updates left; no push or pop.  A storage variable (`old`) bound
by an update, read at a path the storage the updates left checks.  A stored
value:
a word, not a copy (`alice = bob;`). -/
def _root_.Solidity.Tm.inL (ρ : Sym) : Tm C s → Bool
  | .pvV _ => true
  | .pvP x =>
    match lookupBy x ρ.env with
    | some (.path _) | some (.val _) => true
    | some .stale | some (.stor _) | none => false
  | .pvS _ | .pvI _ => false
  | .app0 o => o.inL
  | .app1 o a => o.inL (a.inL ρ)
  | .app2 o a b => o.inL ρ a (a.inL ρ) (b.inL ρ)
  | .app3 o a b c => o.inL a (a.inL ρ) (b.inL ρ) (c.inL ρ)


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
  | bool b => simp [Value.asInt] at hj
  | int n =>
    simp only [Value.asInt, Except.ok.injEq] at hj
    subst hj
    by_cases hn : n < 0 <;>
      simp [payGuard, LTerm.eval, ha, evalBinop, applyBinOp, Value.asInt, checkArith,
        pickBranch, hn, bind, Except.bind]

/-- One update: the term that has to return, and the names it binds. -/
def _root_.Solidity.UpdElem.toL (ρ : Sym) : UpdElem C → LTerm × Sym
  | .val x t => (t.toL ρ, { ρ with env := (x, .val (t.toL ρ)) :: ρ.env })
  | .path x p =>
    (guardPath ρ.stor (p.toL ρ), { ρ with env := (x, .path (p.toL ρ)) :: ρ.env })
  | .storage s =>
    (.sok (s.toL ρ), { stor := s.toL ρ, env := ρ.env.map fun b => (b.1, b.2.onWrite) })
  | .store x s => (.sok (s.toL ρ), { ρ with env := (x, .stor (s.toL ρ)) :: ρ.env })
  -- a ledger entry: it returns where the address and the amount are integers,
  -- which `kite` asks; the ledger itself is not pushed in (nothing reads it)
  | .net r _ a => (.kite (r.toL ρ) (a.toL ρ) (.lit (.bool true)) (.lit (.bool true)), ρ)
  -- a payment: the same, and the amount not negative
  | .pay r a => (.kite (r.toL ρ) (a.toL ρ) (payGuard (a.toL ρ)) (payGuard (a.toL ρ)), ρ)
  | .mref .. | .memory .. | .selfBalance .. | .saveNet .. => (.err, ρ)

/-- An update in the fragment: a local, an alias, the storage, a storage
variable bound to it, or a ledger entry (`transfer`'s, which no term of the
fragment reads); no memory, no funds. -/
def _root_.Solidity.UpdElem.inL (ρ : Sym) : UpdElem C → Bool
  | .val _ t => t.inL ρ
  | .path _ p => p.inL ρ
  | .storage s | .store _ s => s.inL ρ
  | .net r _ a | .pay r a => r.inL ρ && a.inL ρ
  | .mref .. | .memory .. | .selfBalance .. | .saveNet .. => false

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
no memory, no push or pop, no copy between locations, and every alias bound
by an update. -/
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
    cases hs : v.save segs new <;> simp [bind, Except.bind]

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

/-- `τ` is what the updates `ρ` stand for, applied in `σ`: its storage is the
stack of writes read in `σ`, and each name holds what its symbol reads in
`σ`. -/
structure Rel (σ : State) (ρ : Sym) (τ : State) : Prop where
  stor : ρ.stor.eval σ = .ok (.struct τ.storage)
  env : ∀ x, EnvRel σ τ x (lookupBy x ρ.env)
  tx : ∀ k, τ.envVal k = σ.envVal k

/-- Before any update, the state is itself. -/
theorem Rel.empty (σ : State) : Rel σ Sym.empty σ := ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- Binding a name keeps the relation: after `uint y = balances[k];`, `y`
holds what `balances[k]` reads. -/
theorem Rel.bind {σ τ : State} {ρ : Sym} (h : Rel σ ρ τ) (x : Var) (b : SymB) (bd : Binding)
    (hb : EnvRel σ (τ.setEnv x bd) x (some b)) :
    Rel σ { ρ with env := (x, b) :: ρ.env } (τ.setEnv x bd) := by
  refine ⟨h.stor, fun y => ?_, fun k => by rw [← h.tx k]; cases k <;> rfl⟩
  by_cases hy : y = x
  · subst hy; simpa [lookupBy] using hb
  · have := h.env y
    simp only [lookupBy, hy, if_false]
    revert this
    have hst : (τ.setEnv x bd).storage = τ.storage := rfl
    rcases lookupBy y ρ.env with _ | ⟨t⟩ | ⟨q⟩ | _ <;>
      simp [EnvRel, State.getEnv_setEnv_ne hy, hst]

/-- A symbol the updates bound reads only what the updates read. -/
theorem lookupBy_vars {x y : Var} {b : SymB} : (env : List (Var × SymB)) →
    lookupBy y env = some b → x ∉ env.flatMap (fun b => b.2.vars) → x ∉ b.vars
  | [], h, _ => by simp [lookupBy] at h
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
  refine ⟨?_, fun y => ?_, fun k => by
    rw [State.envVal_setEnv, State.envVal_setEnv, h.tx k]⟩
  · show LStor.eval (σ.setEnv x (.val v)) ρ.stor = _
    rw [LStor.eval_setEnv _ hx.1]; exact h.stor
  · by_cases hy : y = x
    · subst hy
      simp only [Sym.free, lookupBy, if_true, EnvRel, LTerm.eval]
      exact ⟨v, by simp only [State.getEnv_setEnv_self]; rfl, by simp⟩
    · have hl : lookupBy y (ρ.free x).env = lookupBy y ρ.env := by
        simp [Sym.free, lookupBy, hy]
      rw [hl]
      have he := h.env y
      rcases hb : lookupBy y ρ.env with _ | ⟨t⟩ | ⟨q⟩ | _ | ⟨S⟩ <;> rw [hb] at he <;>
        simp only [EnvRel] at he ⊢ <;>
        simp only [State.getEnv_setEnv_ne hy]
      · exact he
      · have hv := lookupBy_vars (x := x) ρ.env hb hx.2
        simp only [SymB.vars] at hv
        rw [LTerm.eval_setEnv _ hv]; exact he
      · have hv := lookupBy_vars (x := x) ρ.env hb hx.2
        simp only [SymB.vars] at hv
        rw [LPath.eval_setEnv _ hv]; exact he
      · exact he
      · have hv := lookupBy_vars (x := x) ρ.env hb hx.2
        simp only [SymB.vars] at hv
        rw [LStor.eval_setEnv _ hv]; exact he

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
    simp [LPath.noAt_eval σ hn h', Seg.isAt]
  | .at _ _, _, hn, _ => by simp [LPath.noAt] at hn

/-- With no index on the way, the live read is the read: `alice.account`. -/
theorem findLive_eq_find : ∀ (v : SVal) (qs : List Seg), qs.any Seg.isAt = false →
    v.findLive qs = v.find qs
  | v, [], _ => by cases v <;> rfl
  | _, .at _ :: _, h => by simp [Seg.isAt] at h
  | v, .field f :: qs, h => by
    have h' : qs.any Seg.isAt = false := by simpa [Seg.isAt] using h
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
      · simp [SVal.findLive, SVal.find]
    | map _ _ => rfl

/-- **One index**: the program's check (`Close.idxOk`) passes exactly where
the live element is there: `values[1]` with two values, `balances[k]`. -/
theorem idx_iff (c : SVal) (k : Int) :
    Close.idxOk k c = .ok () ↔ ∃ c', c.findLive [.at k] = .ok c' := by
  cases c with
  | prim p => simp [Close.idxOk, SVal.findLive]
  | struct _ => simp [Close.idxOk, SVal.findLive]
  | array elems shadow fx =>
    by_cases hk : 0 ≤ k ∧ k.toNat < elems.length
    · simp [Close.idxOk, SVal.findLive, hk]
    · simp [Close.idxOk, SVal.findLive, hk]
  | map entries dflt =>
    simp only [Close.idxOk, SVal.findLive, true_iff]
    cases lookupBy k entries <;> simp

/-- A live write whose path reads live is the write. -/
theorem saveLive_eq_save : ∀ {v : SVal} {qs : List Seg} {c : SVal} (new : SVal),
    v.findLive qs = .ok c → v.saveLive qs new = v.save qs new
  | v, [], _, _, _ => by cases v <;> rfl
  | .prim _, _ :: _, _, _, h => by simp [SVal.findLive] at h
  | .struct fields, .field f :: qs, _, new, h => by
    simp only [SVal.findLive] at h
    simp only [SVal.saveLive, SVal.save]
    split at h
    · rename_i o hl
      rw [hl]
      simp only [saveLive_eq_save new h]
    · simp at h
  | .struct _, .at _ :: _, _, _, h => by simp [SVal.findLive] at h
  | .array elems shadow fx, .at i :: qs, _, new, h => by
    simp only [SVal.findLive] at h
    split at h
    · rename_i hi
      have hi' : 0 ≤ i ∧ i.toNat < (elems ++ shadow).length := ⟨hi.1, by simp; omega⟩
      simp only [SVal.saveLive, SVal.save, dif_pos hi, dif_pos hi', List.get_eq_getElem,
        List.getElem_append_left hi.2]
      rw [List.get_eq_getElem] at h
      rw [saveLive_eq_save new h]
      cases (elems[i.toNat]'hi.2).save qs new with
      | error _ => rfl
      | ok u =>
        simp only [bind, Except.bind]
        rw [List.set_append_left _ _ hi.2]
        simp
    · simp at h
  | .array _ _ _, .field _ :: _, _, _, _ => by simp [SVal.saveLive, SVal.save]
  | .map entries dflt, .at i :: qs, _, new, h => by
    simp only [SVal.findLive] at h
    simp only [SVal.saveLive, SVal.save]
    split at h <;> rename_i hl <;> rw [hl] <;> simp only [saveLive_eq_save new h]
  | .map _ _, .field _ :: _, _, _, _ => by simp [SVal.saveLive, SVal.save]

/-- A live write returns only where the live read does. -/
theorem findLive_of_saveLive : ∀ {v : SVal} {qs : List Seg} {new u : SVal},
    v.saveLive qs new = .ok u → ∃ c, v.findLive qs = .ok c
  | v, [], _, _, _ => ⟨v, by cases v <;> rfl⟩
  | .prim _, s :: _, _, _, h => by cases s <;> simp [SVal.saveLive] at h
  | .struct fields, .field f :: qs, _, _, h => by
    simp only [SVal.saveLive] at h
    simp only [SVal.findLive]
    split at h
    · rename_i o hl
      obtain ⟨_, hu, _⟩ := Res.bind_eq_ok.1 h
      rw [hl]
      exact findLive_of_saveLive hu
    · simp at h
  | .struct _, .at _ :: _, _, _, h => by simp [SVal.saveLive] at h
  | .array elems shadow fx, .at i :: qs, _, _, h => by
    simp only [SVal.saveLive] at h
    simp only [SVal.findLive]
    split at h
    · rename_i hi
      obtain ⟨_, hu, _⟩ := Res.bind_eq_ok.1 h
      rw [dif_pos hi]
      exact findLive_of_saveLive hu
    · simp at h
  | .array _ _ _, .field _ :: _, _, _, h => by simp [SVal.saveLive] at h
  | .map entries dflt, .at i :: qs, _, _, h => by
    simp only [SVal.saveLive] at h
    simp only [SVal.findLive]
    split at h <;> rename_i hl <;> rw [hl] <;>
      (obtain ⟨_, hu, _⟩ := Res.bind_eq_ok.1 h; exact findLive_of_saveLive hu)
  | .map _ _, .field _ :: _, _, _, h => by simp [SVal.saveLive] at h

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
  simp [lastAtSegs, Seg.isAt]

/-- An index is the last one. -/
theorem lastAtSegs_at (qs : List Seg) (k : Int) :
    lastAtSegs (qs ++ [.at k]) = qs ++ [.at k] := by
  simp [lastAtSegs, Seg.isAt]

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
    simpa using hall s hs

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
  simpa using h s (List.mem_reverse.mp hs)

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
  | .root _, _, h => by cases h; exact ⟨fun _ => rfl, fun _ h => by simp [LPath.lastAt] at h⟩
  | .field q f, _, h => by
    obtain ⟨qs', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    obtain ⟨h₁, h₂⟩ := LPath.lastAt_eval σ h'
    refine ⟨fun hn => ?_, fun q' hs => ?_⟩
    · simp [h₁ hn, Seg.isAt]
    · rw [lastAtSegs_field]; exact h₂ q' hs
  | .at q k, _, h => by
    refine ⟨fun hn => by simp [LPath.lastAt] at hn, fun q' hs => ?_⟩
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

/-- A write to the storage keeps what the names hold, an alias through an
index made stale. -/
theorem lookupBy_onWrite (y : Var) : ∀ (env : List (Var × SymB)),
    lookupBy y (env.map fun b => (b.1, b.2.onWrite)) = (lookupBy y env).map SymB.onWrite
  | [] => rfl
  | (x, b) :: rest => by
    by_cases hy : y = x <;> simp [lookupBy, hy, lookupBy_onWrite y rest]

/-- A write to the storage keeps the relation of each name. -/
theorem EnvRel.onWrite {σ τ τ' : State} {y : Var} {o : Option SymB}
    (h : EnvRel σ τ y o) (he : τ'.getEnv y = τ.getEnv y) : EnvRel σ τ' y (o.map SymB.onWrite) := by
  rcases o with _ | ⟨t⟩ | ⟨q⟩ | _ | ⟨s⟩
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

section
variable {σ τ : State} {ρ : Sym}

mutual

/-- **A term reads, pushed in, what it read after the updates.**  Example:
after `balances[k] = 5;`, the local `y` of `uint y = balances[k];` is the
term `find(save(storage, balances[k], 5), balances[k])`, read in the state
before the write. -/
theorem Term.toL_eval (h : Rel σ ρ τ) :
    (t : Term C) → t.inL ρ = true → Sim ((t.toL ρ).eval σ) (t.eval τ)
  | .lit _, _ => Sim.refl _
  | .env k, _ => by
    rw [Close.Term.eval_env, h.tx k]
    exact Sim.refl _
  | .pv x, _ => by
    have hx := h.env x
    rw [Close.Term.eval_pv]
    apply Sim.of_eq
    rcases hl : lookupBy x ρ.env with _ | ⟨t⟩ | ⟨q⟩ | _ | ⟨S⟩ <;> rw [hl] at hx <;>
      simp only [EnvRel] at hx <;> simp only [Tm.toL, hl]
    · rw [hx]; rfl
    · obtain ⟨v, h₁, h₂⟩ := hx; rw [h₁, h₂]; rfl
    · obtain ⟨r, segs, _, h₂, _⟩ := hx; rw [h₂]; rfl
    · obtain ⟨r, segs, h₂⟩ := hx; rw [h₂]; rfl
    · obtain ⟨st, -, h₂⟩ := hx; rw [h₂]; rfl
  | .binop op p a b, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    rw [Close.Term.eval_binop]
    simp only [Tm.toL, Op2.toLAt, Op2.toL, LTerm.eval]
    exact Sim.bind (Term.toL_eval h a hf.1) fun _ => evalBinop_sim (Term.toL_eval h b hf.2)
  | .unop op p a, hf => by
    simp only [Tm.inL, Op1.inL] at hf
    rw [Close.Term.eval_unop]
    simp only [Tm.toL, Op1.toL, LTerm.eval]
    exact Sim.bind (Term.toL_eval h a hf) fun _ => Sim.refl _
  | .find s p, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true, Bool.or_eq_true] at hf
    obtain ⟨hs | hs, hf⟩ := hf
    · obtain rfl := STerm.isStorage_eq hs
      have hb := live_bridge (PTerm.toL_chk h p hf)
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
      have hA := PTerm.toL_chk h p hf
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
  | .len s p, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨hs, hf⟩ := hf
    obtain rfl := STerm.isStorage_eq hs
    have hb := live_bridge (PTerm.toL_chk h p hf)
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
  | .ite c a b, hf => by
    simp only [Tm.inL, Op3.inL, Bool.and_eq_true] at hf
    rw [Close.Term.eval_ite]
    simp only [Tm.toL, Op3.toL, LTerm.eval]
    exact Sim.bind (Term.toL_eval h c hf.1.1) fun _ =>
      pickBranch_sim (Term.toL_eval h a hf.1.2) (Term.toL_eval h b hf.2)
  | .read _ _, hf | .net _, hf | .netOf _ _, hf => by simp [Tm.inL, Op1.inL, Op2.inL] at hf

/-- **A path, pushed in, is the path the program took**: the program's
path returns exactly where the path pushed in does and every index on it is
in bounds of the storage the updates left (`LiveTo`).  Example: `values[i]`
returns in neither where `i` is past the end. -/
theorem PTerm.toL_chk (h : Rel σ ρ τ) :
    (p : PTerm C) → p.inL ρ = true → ∀ (qs : List Seg),
      (∃ rs, p.eval τ = .ok rs ∧ qs = .field rs.1 :: rs.2) ↔
        ((p.toL ρ).eval σ = .ok qs ∧ LiveTo (.struct τ.storage) qs)
  | .root r, _, qs => by
    simp only [Tm.toL, Op0.toL, LPath.eval, tm_eval]
    constructor
    · rintro ⟨rs, hrs, rfl⟩
      cases hrs
      exact ⟨rfl, LiveTo.of_noAt _ rfl⟩
    · rintro ⟨hq, -⟩
      cases hq
      exact ⟨(r, []), rfl, rfl⟩
  | .pv x, hf, qs => by
    have hx := h.env x
    rw [Close.PTerm.eval_pv]
    simp only [Tm.inL] at hf
    rcases hl : lookupBy x ρ.env with _ | ⟨t⟩ | ⟨q⟩ | _ | ⟨S⟩ <;> rw [hl] at hx hf <;>
      simp only [EnvRel, Bool.false_eq_true] at hx hf <;>
      simp only [Tm.toL, hl]
    · obtain ⟨v, _, h₂⟩ := hx
      simp [h₂, LPath.stuck, LPath.eval, LTerm.eval, Close.bindingPath, bind, Except.bind]
    · obtain ⟨r, segs, h₁, h₂, hlive⟩ := hx
      simp only [h₂, h₁, Res.ok_bind, Close.bindingPath]
      constructor
      · rintro ⟨rs, hrs, rfl⟩
        cases hrs
        exact ⟨rfl, hlive⟩
      · rintro ⟨hq, -⟩
        cases hq
        exact ⟨(r, segs), rfl, rfl⟩
  | .field p f, hf, qs => by
    simp only [Tm.inL, Op1.inL] at hf
    rw [Close.PTerm.eval_field]
    simp only [Tm.toL, Op1.toL, LPath.eval]
    constructor
    · rintro ⟨rs', hrs', rfl⟩
      obtain ⟨rs, hrs, he⟩ := Res.bind_eq_ok.1 hrs'
      cases he
      obtain ⟨hq, hl⟩ := (PTerm.toL_chk h p hf _).1 ⟨rs, hrs, rfl⟩
      refine ⟨by rw [hq]; rfl, ?_⟩
      show LiveTo _ ((.field rs.1 :: rs.2) ++ [.field f])
      unfold LiveTo
      rw [lastAtSegs_field]
      exact hl
    · rintro ⟨hq, hl⟩
      obtain ⟨qs₀, hq₀, he⟩ := Res.bind_eq_ok.1 hq
      cases he
      have hl₀ : LiveTo (.struct τ.storage) qs₀ := by unfold LiveTo at hl ⊢; rw [lastAtSegs_field] at hl; exact hl
      obtain ⟨rs, hrs, rfl⟩ := (PTerm.toL_chk h p hf qs₀).2 ⟨hq₀, hl₀⟩
      exact ⟨(rs.1, rs.2 ++ [.field f]), by rw [hrs]; rfl, by simp⟩
  | .at p i, hf, qs => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    have hi := Term.toL_eval h i hf.2
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
      obtain ⟨hq, hl⟩ := (PTerm.toL_chk h p hf.1 _).1 ⟨rs, hrs, rfl⟩
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
      obtain ⟨rs, hrs, rfl⟩ := (PTerm.toL_chk h p hf.1 qs₀).2 ⟨hq₀, hl₀⟩
      refine ⟨(rs.1, rs.2 ++ [.at k]), ?_, by simp⟩
      have hfs : τ.findStorage rs.1 rs.2 = .ok c := by rw [← find_root, hl₀.find_eq]; exact hc
      rw [hrs, Res.ok_bind, (hi v).1 hv, Res.ok_bind, hk, Res.ok_bind, Close.checkIndex_eq,
        hfs, Res.ok_bind, (idx_iff c k).2 ⟨c', hck⟩, Res.ok_bind]
  | .next _, hf, _ => by simp [Tm.inL, Op1.inL] at hf
  | .nextIn _ _, hf, _ => by simp [Tm.inL, Op2.inL] at hf
  | .atIn _ _ _, hf, _ => by simp [Tm.inL, Op3.inL] at hf

end

/-- A storage term, pushed in, is the write it made.  Example:
`delAt(storage, alice.account)`. -/
theorem STerm.toL_eval (h : Rel σ ρ τ) :
    (s : STerm C) → s.inL ρ = true →
      Sim ((s.toL ρ).eval σ) (s.eval τ >>= fun τ' => .ok (.struct τ'.storage))
  | .app0 .storage, _ => Sim.of_eq (by rw [Tm.toL, Op0.toL, h.stor]; rfl)
  | .app3 .save s p v, hf => by
    simp only [Tm.inL, Op3.inL, Bool.and_eq_true] at hf
    obtain ⟨⟨hs, hp⟩, hv⟩ := hf
    obtain rfl := STerm.isStorage_eq hs
    match v, hv with
    | .app1 .sval t, hv =>
      have hf : p.inL ρ = true ∧ t.inL ρ = true := ⟨hp, hv⟩
      have ht := Term.toL_eval h t hf.2
      have hb := live_bridge (PTerm.toL_chk h p hf.1)
      rw [Close.STerm.eval_save]
      simp only [Tm.toL, Op0.toL, Op1.toL, Op3.toL, LStor.eval, h.stor, Res.ok_bind, Close.STerm.eval_storage]
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
    | .app1 (.newArr _) _, hv | .app2 .sfind _ _, hv | .app2 .copyMem _ _, hv =>
      simp [Tm.inL, Op1.inL, Op2.inL] at hv
  | .app2 .delAt s p, hf => by
    simp only [Tm.inL, Op2.inL, Bool.and_eq_true] at hf
    obtain ⟨hs, hf⟩ := hf
    obtain rfl := STerm.isStorage_eq hs
    have hb := live_bridge (PTerm.toL_chk h p hf)
    rw [Close.STerm.eval_delAt]
    simp only [Tm.toL, Op0.toL, Op2.toLAt, Op2.toL, LStor.eval, h.stor, Res.ok_bind, Close.STerm.eval_storage]
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
  | .pvS _, hf => by simp [Tm.inL] at hf
  | .app3 .push _ _ _, hf => by simp [Tm.inL, Op3.inL] at hf
  | .app1 (.select _) _, hf => by simp [Tm.inL, Op1.inL] at hf
  | .app2 (.pushSlot _) _ _, hf | .app2 .pop _ _, hf | .app2 .shrink _ _, hf
  | .app2 (.extend _) _ _, hf => by simp [Tm.inL, Op2.inL] at hf

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
  cases g.eval σ <;> simp

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
    have : ¬ ∃ v, g.eval σ = .ok v := by simp [hg]
    cases m <;> simp [guardM_box, guardM_diamond, this, Modality.after, Modality.onHalt]
  | ok τ' =>
    have : ∃ v, g.eval σ = .ok v := by simp [hg]
    cases m <;> simp [guardM_box, guardM_diamond, this, Modality.after, hψ τ' rfl]

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
      simp_all
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
      exact ⟨v, (ht v).2 hv, by simp⟩
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
      exact ⟨rs.1, rs.2, hq, by simp, hl⟩
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
        fun k => by rw [← h.tx k]; cases k <;> rfl⟩ hf.2
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
      exact ⟨τ₁.storage, (hs _).2 (by rw [h₁]; rfl), by simp⟩
    | net r op a =>
      have hra : r.inL ρ = true ∧ a.inL ρ = true := by simpa [UpdElem.inL] using hf.1
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
        exact Fml.toL_holds φ ⟨h.stor, fun y => h.env y, fun k => h.tx k⟩ hf.2
    | pay r a =>
      have hra : r.inL ρ = true ∧ a.inL ρ = true := by simpa [UpdElem.inL] using hf.1
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
          exact Fml.toL_holds φ ⟨h.stor, fun y => h.env y, fun k => h.tx k⟩ hf.2
    | mref _ _ | memory _ | selfBalance _ _ | saveNet _ =>
      simp [UpdElem.inL] at hf
  | .modal m P φ, _, _, _, _, hf => by
    obtain ⟨ω, rfl⟩ := Prog.reverts_eq hf
    cases m <;> simp only [holds, Prog.run, Stmt.run, bind, Except.bind, Modality.afterRun,
      Modality.after, Modality.onHalt, Fml.toL, LFml.holds, not_true_eq_false, ne_eq,
      Except.error.injEq, reduceCtorEq, not_false_eq_true, and_true]
  | .all x p φ, σ, τ, ρ, h, hf => by
    simp only [Fml.inL, Bool.and_eq_true, Bool.not_eq_true'] at hf
    have hx : x ∉ ρ.vars := by simpa using hf.1
    simp only [holds, Fml.toL, LFml.holds]
    exact forall_congr' fun v => imp_congr_right fun _ => Fml.toL_holds φ (h.free hx v) hf.2
  | .upd _ (_ :: _ :: _) _, _, _, _, _, hf | .havoc _, _, _, _, _, hf => by
    simp [Fml.inL] at hf

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
  | prim p => cases s <;> simp [SVal.saveLive] at h
  | struct fields =>
    cases s with
    | «at» _ => simp [SVal.saveLive] at h
    | field n =>
      simp only [SVal.saveLive] at h
      split at h
      · obtain ⟨_, _, he⟩ := Res.bind_eq_ok.1 h; cases he; exact .inl ⟨_, _, rfl, rfl⟩
      · simp at h
  | array elems shadow fx =>
    cases s with
    | field _ => simp [SVal.saveLive] at h
    | «at» i =>
      simp only [SVal.saveLive] at h
      split at h
      · obtain ⟨_, _, he⟩ := Res.bind_eq_ok.1 h; cases he
        exact .inr (.inl ⟨_, _, _, _, rfl, rfl, List.length_set⟩)
      · simp at h
  | map entries dflt =>
    cases s with
    | field _ => simp [SVal.saveLive] at h
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
    | prim p => cases s <;> simp [SVal.saveLive] at h
    | struct fields =>
      cases s with
      | «at» _ => simp [SVal.saveLive] at h
      | field n =>
        simp only [List.cons_append, SVal.saveLive] at h
        split at h
        · rename_i old hl
          obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h; cases he
          obtain ⟨w, w', h₁, h₂, h₃⟩ := save_through Q R hu
          exact ⟨w, w', by simp [SVal.findLive, hl, h₁], h₂, by simp [SVal.findLive, h₃]⟩
        · simp at h
    | array elems shadow fx =>
      cases s with
      | field _ => simp [SVal.saveLive] at h
      | «at» i =>
        simp only [List.cons_append, SVal.saveLive] at h
        split at h
        · rename_i hi
          obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h; cases he
          obtain ⟨w, w', h₁, h₂, h₃⟩ := save_through Q R hu
          refine ⟨w, w', by simp [SVal.findLive, hi, ← h₁], h₂, ?_⟩
          simp [SVal.findLive, hi, h₃]
        · simp at h
    | map entries dflt =>
      cases s with
      | field _ => simp [SVal.saveLive] at h
      | «at» i =>
        simp only [List.cons_append, SVal.saveLive] at h
        split at h <;> rename_i hl
        · obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h; cases he
          obtain ⟨w, w', h₁, h₂, h₃⟩ := save_through Q R hu
          exact ⟨w, w', by simp [SVal.findLive, hl, h₁], h₂, by simp [SVal.findLive, h₃]⟩
        · obtain ⟨upd, hu, he⟩ := Res.bind_eq_ok.1 h; cases he
          obtain ⟨w, w', h₁, h₂, h₃⟩ := save_through Q R hu
          exact ⟨w, w', by simp [SVal.findLive, hl, h₁], h₂, by simp [SVal.findLive, h₃]⟩

/-- No segment is a `length`: the one field an array answers to, and the
one a program never writes. -/
def NoLen (ps : List Seg) : Prop := ∀ s ∈ ps, s ≠ .field "length"

/-- A run followed by a return returns when the run does. -/
theorem ex_ok_bind {α β : Type} {x : Res α} {f : α → β} :
    (∃ u, (x >>= fun a => .ok (f a)) = .ok u) ↔ ∃ a, x = .ok a := by
  cases x <;> simp [bind, Except.bind]

/-- **A write succeeds where a read does**, `length` aside: `alice.age = 3;`
runs exactly where `alice.age` names a location. -/
theorem save_ok_iff_find_ok {new : SVal} : ∀ {v : SVal} {ps : List Seg}, NoLen ps →
    ((∃ u, v.saveLive ps new = .ok u) ↔ ∃ w, v.findLive ps = .ok w)
  | v, [], _ => by cases v <;> simp [SVal.saveLive, SVal.findLive]
  | v, s :: ps, hn => by
    have hn' : NoLen ps := fun t ht => hn t (.tail _ ht)
    have hs : s ≠ .field "length" := hn s (.head _)
    cases v with
    | prim p => cases s <;> simp [SVal.saveLive, SVal.findLive]
    | struct fields =>
      cases s with
      | «at» _ => simp [SVal.saveLive, SVal.findLive]
      | field n =>
        simp only [SVal.saveLive, SVal.findLive]
        cases lookupBy n fields with
        | none => simp
        | some old => simp only [ex_ok_bind]; exact save_ok_iff_find_ok hn'
    | array elems shadow fx =>
      cases s with
      | field n =>
        have : n ≠ "length" := fun h => hs (by rw [h])
        simp [SVal.saveLive, SVal.findLive]
      | «at» i =>
        simp only [SVal.saveLive, SVal.findLive]
        split
        · simp only [ex_ok_bind]; exact save_ok_iff_find_ok hn'
        · simp
    | map entries dflt =>
      cases s with
      | field _ => simp [SVal.saveLive, SVal.findLive]
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
    cases lookupBy f fields <;> simp [bind, Except.bind]
  | array elems shadow fx =>
    by_cases hf : f = "length"
    · subst hf
      cases fx <;> simp [SVal.defaultOf, SVal.findLive, bind, Except.bind]
    · cases fx <;> simp [SVal.defaultOf, SVal.findLive, bind, Except.bind]
  | map _ _ => rfl

/-- **Below a delete, at a key**: a mapping keeps its entries; a fixed-size
array keeps its elements, each deleted in place; anything else has no key to
read (a dynamic array is emptied). -/
theorem defaultOf_key (N : SVal) (k : Int) (more : List Seg) (a : SVal) :
    N.defaultOf.findLive (.at k :: more) = .ok a ↔
      (isMapV N = true ∧ N.findLive (.at k :: more) = .ok a) ∨
      (isFixV N = true ∧ ∃ e, N.findLive [.at k] = .ok e ∧ e.defaultOf.findLive more = .ok a) := by
  cases N with
  | prim p => cases p <;> simp [SVal.defaultOf, SVal.findLive, isMapV, isFixV]
  | struct _ => simp [SVal.defaultOf, SVal.findLive, isMapV, isFixV]
  | array elems shadow fx =>
    cases fx
    · simp [SVal.defaultOf, SVal.findLive, isMapV, isFixV]
    · simp only [SVal.defaultOf, SVal.findLive, isMapV, isFixV, defaultOfElems_eq_map,
        List.length_map, List.get_eq_getElem, List.getElem_map, SVal.findLive_nil]
      by_cases hb : 0 ≤ k ∧ k.toNat < elems.length
      · simp [hb]
      · simp [hb]
  | map _ _ => simp [SVal.defaultOf, isMapV, isFixV]

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
  | c, .at _ :: _, h => by simp [Seg.isAt] at h
  | c, .field n :: r, h => by
    have hr : r.any Seg.isAt = false := by simpa [Seg.isAt] using h
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
    simp [segsEval, segsEval_append σ ha' hb, bind, Except.bind]
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
    simp [Seg.isAt, SSeg.isKey, segsEval_any σ h']
  | .key k :: xs, a, h => by
    obtain ⟨i, _, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨a', _, he⟩ := Res.bind_eq_ok.1 h; cases he
    simp [Seg.isAt, SSeg.isKey]

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
      simp
    · cases hk
  · split at hk
    · cases hk
      subst_vars
      rw [ha] at hb
      cases hb
      simp
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
  | eq => simp_all [PathRel.Holds]
  | above => obtain ⟨f, t, h⟩ := h; exact ⟨f, t, by simp [h]⟩
  | below k => obtain ⟨f, t, h, hk⟩ := h; exact ⟨f, t, by simp [h], hk⟩
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
      simpa [cmpSegs] using (cmpSegs_holds σ xs ys ha hb).cons (.field f)
    · simp only [cmpSegs, hfg, if_false, CaseTree.get]
      exact .inl (by simpa using hfg)
  | .key i :: xs, .key j :: ys, ps, qs, hp, hq => by
    obtain ⟨a, ha, hp⟩ := Res.bind_eq_ok.1 hp
    obtain ⟨as, has, he⟩ := Res.bind_eq_ok.1 hp; cases he
    obtain ⟨b, hb, hq⟩ := Res.bind_eq_ok.1 hq
    obtain ⟨bs, hbs, he⟩ := Res.bind_eq_ok.1 hq; cases he
    rcases hk : keyCmp i j with _ | _ | _
    · simp only [cmpSegs, hk, CaseTree.get, ha, hb, keyEq]
      by_cases hab : a = b
      · subst hab
        simpa using (cmpSegs_holds σ xs ys has hbs).cons (.at a)
      · simp only [hab, decide_false, Bool.false_eq_true, if_false]
        exact .inl (by simpa using hab)
    · have hab : a ≠ b := by simpa using keyCmp_spec hk ha hb
      simp only [cmpSegs, hk, CaseTree.get]
      exact .inl (by simpa using hab)
    · have hab : a = b := by simpa using keyCmp_spec hk ha hb
      subst hab
      simpa [cmpSegs, hk] using (cmpSegs_holds σ xs ys has hbs).cons (.at a)
  | .field f :: xs, .key j :: ys, ps, qs, hp, hq => by
    obtain ⟨a, ha, he⟩ := Res.bind_eq_ok.1 hp; cases he
    obtain ⟨b, hb, hq⟩ := Res.bind_eq_ok.1 hq
    obtain ⟨bs, hbs, he⟩ := Res.bind_eq_ok.1 hq; cases he
    exact .inl (by simp)
  | .key i :: xs, .field g :: ys, ps, qs, hp, hq => by
    obtain ⟨a, ha, hp⟩ := Res.bind_eq_ok.1 hp
    obtain ⟨as, has, he⟩ := Res.bind_eq_ok.1 hp; cases he
    obtain ⟨b, hb, he⟩ := Res.bind_eq_ok.1 hq; cases he
    exact .inl (by simp)

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
termination_by structural s => s

/-- The word at `Q` in `s`, where `s` and `Q` return. -/
def LStor.readU : LStor → LPath → LTerm
  | .init, Q => .find .init Q
  | .save s P w, Q => (cmpSegs P.elim.segs Q.segs).toTerm (saveLeaf w.elim (s.readU Q))
  | .del s P, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (delLeaf (s.readU Q) P.elim fun sh q => s.mapU sh q)
termination_by structural s => s

/-- Whether `Q` names a location of `s`, where `s` and `Q` return. -/
def LStor.hasU : LStor → LPath → LTerm
  | .init, Q => .has .init Q
  | .save s P _, Q => (cmpSegs P.elim.segs Q.segs).toTerm (saveHas (s.hasU Q))
  | .del s P, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (delHas (s.hasU Q) P.elim fun sh q => s.mapU sh q)
termination_by structural s => s

/-- The length of the array at `Q` in `s`, where `s` and `Q` return: a
write keeps the length of every array above it, as it keeps its shape. -/
def LStor.lenU : LStor → LPath → LTerm
  | .init, Q => .len .init Q
  | .save s P _, Q => (cmpSegs P.elim.segs Q.segs).toTerm (saveMap (s.lenU Q))
  | .del s P, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (delLen (s.lenU Q) (lenEnd (s.lenU Q) (s.mapU .fixed Q)) P.elim fun sh q => s.mapU sh q)
termination_by structural s => s

/-- Whether `Q` names a mapping (`sh = .map`) or a fixed-size array
(`.fixed`) of `s`, where `s` and `Q` return. -/
def LStor.mapU (sh : KShape) : LStor → LPath → LTerm
  | .init, Q => .kmap sh .init Q
  | .save s P _, Q => (cmpSegs P.elim.segs Q.segs).toTerm (saveMap (s.mapU sh Q))
  | .del s P, Q => (cmpSegs P.elim.segs Q.segs).toTerm
      (delMap (s.mapU sh Q) P.elim fun sh' q => s.mapU sh' q)
termination_by structural s => s

end

/-- A formula with every read of a write eliminated. -/
def LFml.elim : LFml → LFml
  | .tt => .tt
  | .eq a b => .eq a.elim b.elim
  | .not φ => .not φ.elim
  | .and φ ψ => .and φ.elim ψ.elim
  | .imp φ ψ => .imp φ.elim ψ.elim
  | .all x p φ => .all x p φ.elim

/-! ### Eliminating keeps what returns -/

/-- Two runs that both halt agree. -/
theorem Sim.halt {α : Type} {x y : Res α} (hx : ∀ a, x ≠ .ok a) (hy : ∀ a, y ≠ .ok a) : Sim x y :=
  fun a => ⟨fun h => absurd h (hx a), fun h => absurd h (hy a)⟩

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
      subst hs; simp

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
    exact ⟨.bool true, (hs _).2 (by simp [hv, Res.ok_bind]), .bool true, ⟨qs, h₂, rfl⟩,
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
  | .field _ :: r => by simp [leadFields, Seg.isAt, leadFields_noAt r]
  | [] => rfl
  | .key _ :: _ => rfl

/-- Segments with a key evaluate to their leading members, then a key. -/
theorem segsEval_leadFields (σ : State) : ∀ {xs : List SSeg} {ys : List Seg},
    segsEval σ xs = .ok ys → xs.any SSeg.isKey = true →
      ∃ k more, ys = leadFields xs ++ .at k :: more
  | [], _, _, hk => by simp at hk
  | .field f :: r, ys, h, hk => by
    obtain ⟨ys', h', he⟩ := Res.bind_eq_ok.1 h; cases he
    obtain ⟨k, more, rfl⟩ := segsEval_leadFields σ h' (by simpa [SSeg.isKey] using hk)
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
  | [], q => by simp [LPath.addFields, leadFields, Close.bind_ok_right]
  | .key _ :: _, q => by simp [LPath.addFields, leadFields, Close.bind_ok_right]

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
    | ok v' => exact absurd ((ha v').2 rfl) (by simp)
    | error _ => exact hb x

/-- A run that returns when a test does, and otherwise falls back. -/
theorem orElseR_eq_ok {a b : Res Value} {x : Value} :
    orElseR a b = .ok x ↔ a = .ok x ∨ ((∀ y, a ≠ .ok y) ∧ b = .ok x) := by
  cases a <;> simp [orElseR]

/-- The length of a default: a fixed-size array keeps its length, a dynamic
one has none left. -/
theorem lenEnd_sim {σ : State} {old fixed : LTerm} {x : Res SVal}
    (ho : Sim (old.eval σ) (x >>= Close.arrLen)) (hf : Sim (fixed.eval σ) (x >>= KShape.fixed.test)) :
    Sim ((lenEnd old fixed).eval σ) (x >>= fun w => Close.arrLen w.defaultOf) := by
  refine (Sim.orElse (Sim.bind hf fun _ => ho) (Sim.bind ho fun _ => Sim.refl _)).trans
    (Sim.of_eq ?_)
  rcases x with e | ⟨(i | b) | fs | ⟨es, sh, _ | _⟩ | ⟨es, d⟩⟩ <;>
    simp [bind, Except.bind, orElseR, KShape.test, isFixV, Close.arrLen, SVal.defaultOf,
      defaultOfElems_eq_map, LTerm.eval]

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
    simp [Res.ok_bind]
  | .field f :: r, q, qs, R, hq, hR, hf => by
    obtain ⟨R', hR', he⟩ := Res.bind_eq_ok.1 hR; cases he
    have hq' : (q.field f).eval σ = .ok (qs ++ [.field f]) := by
      simp [LPath.eval, hq, Res.ok_bind]
    have ih := delBelow_sim hg hMap hEnd r (q.field f) (qs ++ [.field f]) R' hq' hR'
      (by rw [← hf]; simp)
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
      (by rw [← hf]; simp)
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
          · simp at hm
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
          · simp at hx
        obtain ⟨e, he, hr⟩ := Res.bind_eq_ok.1 (by
          have := (ih a).1 h₂; rw [SVal.findLive_append, bind_assoc, hN, Res.ok_bind] at this
          exact this)
        obtain ⟨b, hb, hG⟩ := Res.bind_eq_ok.1 hr
        exact ⟨N, hN, b, (defaultOf_key N i R' b).2 (.inr ⟨hfix, e, he, hb⟩), hG⟩
    · rintro ⟨N, hN, b, hb, hG⟩
      rcases (defaultOf_key N i R' b).1 hb with ⟨hmap, hb'⟩ | ⟨hfix, e, he, hb'⟩
      · refine .inl ⟨.bool true, (hgm _).2 ?_, (hMap a).2 ?_⟩
        · simp [hN, Res.ok_bind, KShape.test, kmapF, hmap]
        · rw [← hf, SVal.findLive_append, bind_assoc, hN, Res.ok_bind, hb', Res.ok_bind, hG]
      · have hnm : isMapV N = false := by
          cases N <;> simp_all [isMapV, isFixV]
        refine .inr ⟨fun y hy => ?_, .bool true, (hgf _).2 ?_, (ih a).2 ?_⟩
        · obtain ⟨z, hz, _⟩ := Res.bind_eq_ok.1 hy
          obtain ⟨N', hN', hm⟩ := Res.bind_eq_ok.1 ((hgm z).1 hz)
          rw [hN] at hN'; cases hN'
          simp [KShape.test, kmapF, hnm] at hm
        · simp [hN, Res.ok_bind, KShape.test, hfix]
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

set_option maxHeartbeats 400000 in
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

/-- Eliminating keeps the path a path term names: `people[balances[a]]` after
`balances[a] = 5;` names `people[5]`. -/
theorem LPath.elim_sim (σ : State) : (q : LPath) → Sim (q.elim.eval σ) (q.eval σ)
  | .root _ => Sim.refl _
  | .field q _ => Sim.bind (LPath.elim_sim σ q) fun _ => Sim.refl _
  | .at q k => Sim.bind (LPath.elim_sim σ q) fun _ =>
      Sim.bind (Sim.bind (LTerm.elim_sim σ k) fun _ => Sim.refl _) fun _ => Sim.refl _

/-- The guard of a storage returns exactly when its writes do. -/
theorem LStor.okE_sim (σ : State) :
    (s : LStor) → Sim (s.okE.eval σ) (s.eval σ >>= fun _ => .ok (.bool true))
  | .init => Sim.refl _
  | .save s q w => by
    simp only [LStor.okE]
    split
    · rename_i hn
      intro a
      simp only [LTerm.eval, LStor.eval, Res.bind_eq_ok]
      constructor
      · rintro ⟨_, h₁, wv, h₂, _, ⟨qs, h₃, -⟩, h₄⟩
        obtain ⟨v, hv, -⟩ := Res.bind_eq_ok.1 ((LStor.okE_sim σ s _).1 h₁)
        have hq := (LPath.elim_sim σ q qs).1 h₃
        obtain ⟨_, hf, he⟩ := Res.bind_eq_ok.1 ((LStor.hasU_sim σ s q.elim hv h₃ a).1 h₄)
        cases he
        obtain ⟨u, hu⟩ := (save_ok_iff_find_ok (new := wv.toSVal) (LPath.noLen_eval σ hn hq)).2
          ⟨_, hf⟩
        exact ⟨u, ⟨wv, (LTerm.elim_sim σ w wv).1 h₂, v, hv, qs, hq, hu⟩, rfl⟩
      · rintro ⟨u, ⟨wv, h₂, v, hv, qs, hq, hu⟩, he⟩
        cases he
        have h₃ := (LPath.elim_sim σ q qs).2 hq
        obtain ⟨c, hc⟩ := (save_ok_iff_find_ok (LPath.noLen_eval σ hn hq)).1 ⟨u, hu⟩
        refine ⟨.bool true, (LStor.okE_sim σ s _).2 (by simp [hv, Res.ok_bind]), wv,
          (LTerm.elim_sim σ w wv).2 h₂, .bool true, ⟨qs, h₃, rfl⟩, ?_⟩
        exact (LStor.hasU_sim σ s q.elim hv h₃ _).2 (by simp [hc, Res.ok_bind])
    · exact Sim.refl _
  | .del s q => by
    simp only [LStor.okE]
    split
    · rename_i hn
      intro a
      simp only [LTerm.eval, LStor.eval, Res.bind_eq_ok]
      constructor
      · rintro ⟨_, h₁, _, ⟨qs, h₃, -⟩, h₄⟩
        obtain ⟨v, hv, -⟩ := Res.bind_eq_ok.1 ((LStor.okE_sim σ s _).1 h₁)
        have hq := (LPath.elim_sim σ q qs).1 h₃
        obtain ⟨c, hf, he⟩ := Res.bind_eq_ok.1 ((LStor.hasU_sim σ s q.elim hv h₃ a).1 h₄)
        cases he
        obtain ⟨u, hu⟩ := (save_ok_iff_find_ok (new := c.defaultOf) (LPath.noLen_eval σ hn hq)).2
          ⟨_, hf⟩
        exact ⟨u, ⟨v, hv, qs, hq, c, hf, hu⟩, rfl⟩
      · rintro ⟨u, ⟨v, hv, qs, hq, c, hc, hu⟩, he⟩
        cases he
        have h₃ := (LPath.elim_sim σ q qs).2 hq
        refine ⟨.bool true, (LStor.okE_sim σ s _).2 (by simp [hv, Res.ok_bind]), .bool true,
          ⟨qs, h₃, rfl⟩, ?_⟩
        exact (LStor.hasU_sim σ s q.elim hv h₃ _).2 (by simp [hc, Res.ok_bind])
    · exact Sim.refl _

/-- **What a read after writes returns**, peeled one write at a time. -/
theorem LStor.readU_sim (σ : State) : (s : LStor) → ∀ (Q : LPath) {v : SVal} {qs : List Seg},
    s.eval σ = .ok v → Q.eval σ = .ok qs → Sim ((s.readU Q).eval σ) (v.findLive qs >>= SVal.asValue)
  | .init, Q, v, qs, hv, hq => by
    cases hv
    simp only [LStor.readU, LTerm.eval, LStor.eval, hq, Res.ok_bind]
    exact Sim.refl _
  | .save s P w, Q, u, qs, hu, hq => by
    obtain ⟨wv, hw, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (LPath.elim_sim σ P ps).2 hp
    rw [LStor.readU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      simp only [saveLeaf, findLive_saveLive_same hu, Res.ok_bind, Close.asValue_toSVal]
      exact Sim.trans (LTerm.elim_sim σ w) (Sim.of_eq hw)
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨_, w', _, hs', hf⟩ := save_through qs (f :: t) hu
      obtain ⟨e, he⟩ := save_cons_asValue hs'
      refine Sim.halt (by simp [saveLeaf, LTerm.eval]) ?_
      simp [hf, he, Res.ok_bind]
    | below k =>
      obtain ⟨f, t, rfl, -⟩ := hr
      refine Sim.halt (by simp [saveLeaf, LTerm.eval]) ?_
      rw [SVal.findLive_append, findLive_saveLive_same hu]
      cases wv <;> simp [Res.ok_bind, find_prim_cons, Res.error_bind]
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact LStor.readU_sim σ s Q hv hq
  | .del s P, Q, u, qs, hu, hq => by
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (LPath.elim_sim σ P ps).2 hp
    rw [LStor.readU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      simp only [delLeaf, LTerm.eval, findLive_saveLive_same hu, Res.ok_bind, asValue_defaultOf]
      have h₁ := LStor.readU_sim σ s Q hv hq
      rw [hc, Res.ok_bind] at h₁
      exact Sim.bind h₁ fun _ => Sim.refl _
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨_, w', _, hs', hf⟩ := save_through qs (f :: t) hu
      obtain ⟨e, he⟩ := save_cons_asValue hs'
      refine Sim.halt (by simp [delLeaf, LTerm.eval]) ?_
      simp [hf, he, Res.ok_bind]
    | below rest =>
      obtain ⟨f, t, rfl, hrest⟩ := hr
      simp only [delLeaf]
      have hEnd : Sim ((LTerm.zero (s.readU Q)).eval σ)
          (v.findLive (ps ++ f :: t) >>= fun w => w.defaultOf.asValue) := by
        simp only [LTerm.eval]
        refine (Sim.bind (LStor.readU_sim σ s Q hv hq) (fun _ => Sim.refl _)).trans
          (Sim.of_eq ?_)
        rw [bind_assoc]; congr 1; funext w; rw [asValue_defaultOf]
      have h := delBelow_sim (v := v) (G := SVal.asValue)
        (fun sh q qs hq' => LStor.mapU_sim σ s sh q hv hq') (LStor.readU_sim σ s Q hv hq) hEnd
        rest P.elim ps (f :: t) hp' hrest rfl
      rw [hc, Res.ok_bind] at h
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind]
      exact h
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact LStor.readU_sim σ s Q hv hq

/-- **Whether a location is there after writes**, peeled one write at a time. -/
theorem LStor.hasU_sim (σ : State) : (s : LStor) → ∀ (Q : LPath) {v : SVal} {qs : List Seg},
    s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.hasU Q).eval σ) (v.findLive qs >>= fun _ => .ok (.bool true))
  | .init, Q, v, qs, hv, hq => by
    cases hv
    simp only [LStor.hasU, LTerm.eval, LStor.eval, hq, Res.ok_bind]
    exact Sim.refl _
  | .save s P w, Q, u, qs, hu, hq => by
    obtain ⟨wv, hw, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (LPath.elim_sim σ P ps).2 hp
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
      refine Sim.halt (by simp [saveHas, LTerm.eval]) ?_
      rw [SVal.findLive_append, findLive_saveLive_same hu]
      cases wv <;> simp [Res.ok_bind, find_prim_cons, Res.error_bind]
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact LStor.hasU_sim σ s Q hv hq
  | .del s P, Q, u, qs, hu, hq => by
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (LPath.elim_sim σ P ps).2 hp
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
        (fun sh q qs hq' => LStor.mapU_sim σ s sh q hv hq') (LStor.hasU_sim σ s Q hv hq)
        (LStor.hasU_sim σ s Q hv hq) rest P.elim ps (f :: t) hp' hrest rfl
      rw [hc, Res.ok_bind] at h
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind]
      exact h
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact LStor.hasU_sim σ s Q hv hq

/-- **Whether a mapping is there after writes**, peeled one write at a time. -/
theorem LStor.mapU_sim (σ : State) : (s : LStor) → ∀ (sh : KShape) (Q : LPath) {v : SVal}
    {qs : List Seg}, s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.mapU sh Q).eval σ) (v.findLive qs >>= sh.test)
  | .init, sh, Q, v, qs, hv, hq => by
    cases hv
    simp only [LStor.mapU, LTerm.eval, LStor.eval, hq, Res.ok_bind]
    exact Sim.refl _
  | .save s P w, sh, Q, u, qs, hu, hq => by
    obtain ⟨wv, hw, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (LPath.elim_sim σ P ps).2 hp
    rw [LStor.mapU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      refine Sim.halt (by simp [saveMap, LTerm.eval]) ?_
      simp only [findLive_saveLive_same hu, Res.ok_bind]
      cases wv <;> cases sh <;> simp [KShape.test, kmapF, isMapV, isFixV, Value.toSVal]
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu
      simp only [saveMap, hf, Res.ok_bind, save_cons_kmapF hs']
      have := LStor.mapU_sim σ s sh Q hv hq
      rw [hw₀, Res.ok_bind] at this
      exact this
    | below rest =>
      obtain ⟨f, t, rfl, -⟩ := hr
      refine Sim.halt (by simp [saveMap, LTerm.eval]) ?_
      rw [SVal.findLive_append, findLive_saveLive_same hu]
      cases wv <;> simp [Res.ok_bind, find_prim_cons, Res.error_bind]
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact LStor.mapU_sim σ s sh Q hv hq
  | .del s P, sh, Q, u, qs, hu, hq => by
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (LPath.elim_sim σ P ps).2 hp
    rw [LStor.mapU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      simp only [delMap, findLive_saveLive_same hu, Res.ok_bind, KShape.test_defaultOf]
      have := LStor.mapU_sim σ s sh Q hv hq
      rw [hc, Res.ok_bind] at this
      exact this
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu
      simp only [delMap, hf, Res.ok_bind, save_cons_kmapF hs']
      have := LStor.mapU_sim σ s sh Q hv hq
      rw [hw₀, Res.ok_bind] at this
      exact this
    | below rest =>
      obtain ⟨f, t, rfl, hrest⟩ := hr
      simp only [delMap]
      have hEnd : Sim ((s.mapU sh Q).eval σ)
          (v.findLive (ps ++ f :: t) >>= fun w => sh.test w.defaultOf) := by
        simp only [KShape.test_defaultOf]; exact LStor.mapU_sim σ s sh Q hv hq
      have h := delBelow_sim (v := v) (G := sh.test)
        (fun sh' q qs hq' => LStor.mapU_sim σ s sh' q hv hq') (LStor.mapU_sim σ s sh Q hv hq)
        hEnd rest P.elim ps (f :: t) hp' hrest rfl
      rw [hc, Res.ok_bind] at h
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind]
      exact h
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact LStor.mapU_sim σ s sh Q hv hq

/-- **The length of an array after writes**, peeled one write at a time. -/
theorem LStor.lenU_sim (σ : State) : (s : LStor) → ∀ (Q : LPath) {v : SVal} {qs : List Seg},
    s.eval σ = .ok v → Q.eval σ = .ok qs →
      Sim ((s.lenU Q).eval σ) (v.findLive qs >>= Close.arrLen)
  | .init, Q, v, qs, hv, hq => by
    cases hv
    simp only [LStor.lenU, LTerm.eval, LStor.eval, hq, Res.ok_bind]
    exact Sim.refl _
  | .save s P w, Q, u, qs, hu, hq => by
    obtain ⟨wv, hw, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (LPath.elim_sim σ P ps).2 hp
    rw [LStor.lenU]
    refine cmp_sim hp' hq fun r hr => ?_
    cases r with
    | eq =>
      simp only [PathRel.Holds] at hr
      subst hr
      refine Sim.halt (by simp [saveMap, LTerm.eval]) ?_
      simp only [findLive_saveLive_same hu, Res.ok_bind]
      cases wv <;> simp [Close.arrLen, Value.toSVal]
    | above =>
      obtain ⟨f, t, rfl⟩ := hr
      obtain ⟨w₀, w', hw₀, hs', hf⟩ := save_through qs (f :: t) hu
      simp only [saveMap, hf, Res.ok_bind, save_cons_arrLen hs']
      have := LStor.lenU_sim σ s Q hv hq
      rw [hw₀, Res.ok_bind] at this
      exact this
    | below rest =>
      obtain ⟨f, t, rfl, -⟩ := hr
      refine Sim.halt (by simp [saveMap, LTerm.eval]) ?_
      rw [SVal.findLive_append, findLive_saveLive_same hu]
      cases wv <;> simp [Res.ok_bind, find_prim_cons, Res.error_bind]
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact LStor.lenU_sim σ s Q hv hq
  | .del s P, Q, u, qs, hu, hq => by
    obtain ⟨v, hv, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨ps, hp, hu⟩ := Res.bind_eq_ok.1 hu
    obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
    have hp' : P.elim.eval σ = .ok ps := (LPath.elim_sim σ P ps).2 hp
    have hEnd := lenEnd_sim (LStor.lenU_sim σ s Q hv hq) (LStor.mapU_sim σ s .fixed Q hv hq)
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
      have := LStor.lenU_sim σ s Q hv hq
      rw [hw₀, Res.ok_bind] at this
      exact this
    | below rest =>
      obtain ⟨f, t, rfl, hrest⟩ := hr
      simp only [delLen]
      have h := delBelow_sim (v := v) (G := Close.arrLen)
        (fun sh' q qs hq' => LStor.mapU_sim σ s sh' q hv hq') (LStor.lenU_sim σ s Q hv hq)
        hEnd rest P.elim ps (f :: t) hp' hrest rfl
      rw [hc, Res.ok_bind] at h
      rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind]
      exact h
    | diverge => rw [findLive_saveLive_diverge hr hu]; exact LStor.lenU_sim σ s Q hv hq

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
      have : ∀ x, a.elim.eval σ ≠ .ok x := fun x hx => by simp [(ha x).1 hx] at h₁
      cases h₂ : a.elim.eval σ with
      | error => simp
      | ok x => exact absurd h₂ (this x)
    | ok x =>
      rw [(ha x).2 h₁]
      cases h₃ : b.eval σ with
      | error e =>
        have : ∀ y, b.elim.eval σ ≠ .ok y := fun y hy => by simp [(hb y).1 hy] at h₃
        cases h₄ : b.elim.eval σ with
        | error => simp
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
  cases a.eval σ <;> cases b.eval σ <;> simp [Modality.wp, Modality.onHalt]

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
