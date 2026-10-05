import Solidity.Calculus.Close
import Solidity.Calculus.MemNames

/-!
# The target language of `sol_decide`

The terms, paths, storages and memories `Calculus/Decide.lean` pushes the
updates into and eliminates the reads of, each read in the state a formula
starts in (`LTerm.eval`, `LMem.run`), and the formulas over them.  It is
apart from the reduction so that the readers of memory
(`Calculus/MemRead.lean`) can sit between the language and the translation
that uses them; the rationale of the language is the reduction's.
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
  | .cpok s q => s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= fun sv =>
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
  | .copySt m k s q => s.eval σ >>= fun v => q.eval σ >>= fun qs => v.findLive qs >>= fun sv =>
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

/-! ## Guards -/

/-- `a`, guarded by `g` returning; `a` alone after a literal. -/
def seqL (g a : LTerm) : LTerm :=
  match g with
  | .lit _ => a
  | g => .seq g a

theorem seqL_eval (σ : State) (g a : LTerm) :
    (seqL g a).eval σ = g.eval σ >>= fun _ => a.eval σ := by
  unfold seqL; split <;> rfl

/-- A test that returns `true` where `t` returns and `false` where it halts. -/
def isT (t : LTerm) : LTerm := .orElse (.seq t (.lit (.bool true))) (.lit (.bool false))

theorem isT_eval (σ : State) (t : LTerm) :
    (isT t).eval σ = .ok (.bool (match t.eval σ with | .ok _ => true | .error _ => false)) := by
  unfold isT
  simp only [LTerm.eval]
  cases t.eval σ <;> rfl

end Decide

end Solidity
