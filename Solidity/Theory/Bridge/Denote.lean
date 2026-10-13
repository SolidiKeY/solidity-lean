import Solidity.Signature

/-!
# What a typed symbol denotes in the Theory, and the bridge

A formula's equation reads its terms in the typed Theory
(`Theory/Typed/Obs.lean`: a value is its observations), KeY's total model:
a read off the end of what is there reads the default, a write always
lands, so solkey's laws need no "the write lands" premise.  `Op0.denote` …
`Op3.denote` read the typed symbols of `Signature.lean` there, over the
typed global part's storage read as its observations (`Storage.obs`);
`Tm.denote` (`Calculus/Lands.lean`) is one recursion over them.  A sort
denotes `Srt.TDen C`: a word or a KeY `int` an `Option` (`none` a halt), a
path a storage location (`SLoc`), a storage a `TSto`, a stored value a
`TVal`.

**The bridge** (`Op0.denote_eval` … `Op3.denote_eval`): where the typed
evaluation returns (`OpN.eval`, `some`), the denotation is its value read
as its observations (`Srt.Bridge`): literally, by the bridge lemmas of
`Theory/Typed/Obs.lean` (`Storage.obs_write`, `obs_delete`, `obs_push`, …).

**Where it does not follow the Theory.**
- Arithmetic is the interpreter's checked arithmetic (`BinOp.evalT`,
  `UnOp.evalT`), a halt `none`.
- The memory island is not abstracted: `read`, `mlen` and `copyMem` denote
  the typed evaluation's value, and the memory sorts denote nothing.
- A path is not bounds-checked (`at`): that is KeY's guard, a premise of the
  laws.  `next` reads the length in the global storage, `nextIn` in its
  storage term.

This is the only Theory module that imports the signature directly (design
R10); `Theory/Typed/Mem.lean` reads it (`MAddrT`, `Grown.writeT`) through
`Calculus/StateFacts.lean`.
-/

namespace Solidity

open Semantics (lookupBy)

variable {C : Contract}

/-! ## The Theory's sorts -/

/-- What a term of each sort denotes in the Theory: a word or a KeY `int`
its value (`none`, a halt), a path a storage location, a storage and a
stored value their observations; the memory sorts denote nothing of their
own. -/
@[reducible] def Srt.TDen (C : Contract) : Srt → Type
  | .val p => Option p.Denote
  | .path T => SLoc C T
  | .st => TSto C
  | .sv T => TVal T
  | .sts s => TSto (Contract.ofStruct s)
  | .spath s T => SLoc (Contract.ofStruct s) T
  | .kint => Option Int
  | .ident _ | .addr _ | .mem | .mv _ => Unit

/-- A live length as a `uint`: past the bound, nothing. -/
def lenW (n : Nat) : Option PrimTy.uint.Denote :=
  if h : n < 2 ^ 256 then some (lenU n h) else none

/-! ## The symbols in the Theory -/

/-- A constant in the Theory. -/
def Op0.denote (g : State C []) {s : Srt} : Op0 C s → s.TDen C
  | .lit v => some v
  | .env k => some (g.envVal k)
  | .root r h => .ref (SRef.ofRoot r h)
  | .storage => g.storage.obs
  | .memory => ()
  | .mtSt => (Storage.init C).obs
  | .member _ f h => .ref (SRef.ofRoot (C := Contract.ofStruct _) f h)
  | .zlit n => some n

/-- A unary symbol in the Theory, its argument's denotation given. -/
def Op1.denote (g : State C []) {a s : Srt} : Op1 C a s → a.TDen C → s.TDen C
  | .unop op _, da => da.bind op.evalT
  | .net, da => da.map fun n => (lookupBy n.1 g.net).getD 0
  | .delValue, da => da.map fun _ => PrimTy.dflt _
  | .field h, dp => ObsLoc.app dp (.field h .nil)
  | .next, dp => ObsLoc.app dp (.at (g.storage.obs.len dp : Int) .nil)
  | .sval, da => TVal.ofWord (da.getD (PrimTy.dflt _))
  | .newArr h, dn => (newArrT _ (dn.getD (PrimTy.dflt _)) h).obs
  | .alloc _ _, _ => ()
  | .mfield _, _ => ()
  | .addM _ _, _ => ()
  | .mval, _ => ()
  | .ref, _ => ()
  | .wt, _ => some true
  | .select _ h, ds => ds.select h
  | .selectIn h, ds => Obs.select (C := Contract.ofStruct _) ds h
  | .fieldIn h, dp => ObsLoc.app dp (.field h .nil)
  | .toInt, da => da.map (·.1)

/-- A binary symbol in the Theory, its arguments' typed readings and
denotations given. -/
def Op2.denote (g : State C []) {a b s : Srt} :
    Op2 C a b s → Option (a.Den C g.H) → Option (b.Den C g.H) → a.TDen C → b.TDen C → s.TDen C
  | .binop op _, _, _, da, db => da.bind fun x => binopT op x db
  | .find, _, _, ds, dp => some (ds.word dp)
  | .len, _, _, ds, dp => lenW (ds.len dp)
  | .read, x, y, _, _ => Op2.eval g .read x y
  | .mlen, x, y, _, _ => Op2.eval g .mlen x y
  | .at it, _, _, dp, di => ObsLoc.app dp (Path.index it (PrimTy.key (di.getD (PrimTy.dflt _))))
  | .nextIn, _, _, ds, dp => ObsLoc.app dp (.at (ds.len dp : Int) .nil)
  | .delAt, _, _, ds, dp => ds.delAt dp
  | .pushSlot, _, _, ds, dp => ds.extend dp
  | .pop, _, _, ds, dp => ds.pop false dp
  | .shrink, _, _, ds, dp => ds.pop true dp
  | .extend, _, _, ds, dp => ds.extend dp
  | .sfind, _, _, ds, dp => ds.find dp
  | .copyMem, x, y, _, _ => match Op2.eval g .copyMem x y with
    | some w => w.obs
    | none => (SVal.dflt _).obs
  | .iread, _, _, _, _ => ()
  | .copy _, _, _, _, _ => ()
  | .mat _, _, _, _, _ => ()
  | .copySt _, _, _, _, _ => ()
  | .findIn, _, _, ds, dp => some (ds.word dp)
  | .delAtIn, _, _, ds, dp => ds.delAt dp
  | .sfindIn, _, _, ds, dp => ds.find dp
  | .zbin op _, _, _, da, db => do some (op.evalZ (← da) (← db))
  | .zcmp op _, _, _, da, db => do some (op.cmpZ (← da) (← db))

/-- A ternary symbol in the Theory, its arguments' denotations given. -/
def Op3.denote {a b c s : Srt} : Op3 C a b c s → a.TDen C → b.TDen C → c.TDen C → s.TDen C
  | .ite, dc, da, db => dc.bind fun x => cond x da db
  | .save, ds, dp, dv => ds.copyTo dp dv
  | .push, ds, dp, dv => ds.push dp (TVal.strip dv)
  | .atIn it, _, dp, di => ObsLoc.app dp (Path.index it (PrimTy.key (di.getD (PrimTy.dflt _))))
  | .write, _, _, _ => ()
  | .saveIn, ds, dp, dv => ds.copyTo dp dv

/-! ## The bridge -/

/-- A denotation agrees with a typed value: the value itself, the
reference, the storage or stored value read as its observations. -/
def Srt.Bridge (C : Contract) (H : HTy) : (s : Srt) → s.TDen C → s.Den C H → Prop
  | .val _, d, x => d = some x
  | .path _, d, r => d = .ref r
  | .st, d, w => d = w.obs
  | .sv _, d, w => d = w.obs
  | .sts _, d, w => d = w.obs
  | .spath _ _, d, r => d = .ref r
  | .kint, d, n => d = some n
  | .ident _, _, _ | .addr _, _, _ | .mem, _, _ | .mv _, _, _ => True

/-- A denotation agrees with a typed reading wherever it returns. -/
def Srt.BridgeO (C : Contract) (H : HTy) (s : Srt) (d : s.TDen C) (x : Option (s.Den C H)) : Prop :=
  ∀ v, x = some v → Srt.Bridge C H s d v

section Bridge

variable (g : State C [])

theorem Storage.obs_len_ref_some {E : Ty} {st : Storage C} {r : SRef C (.ref (.array E))}
    {w : SVal (.ref (.array E))} (h : st.find r = some w) :
    st.obs.len (.ref r) = (SVal.view w : ArrView E).n := by
  have e := congrArg (fun o : TVal _ => o.len .nil) (Storage.obs_find_some h)
  simp only [Obs.find_len] at e
  rw [show (ObsLoc.app (SLoc.ref r) .nil : SLoc C _) = .ref r from congrArg SLoc.ref
    (SRef.append_nil r)] at e
  rw [e]
  cases w; rfl

theorem Storage.obs_word_ref_some {P : PrimTy} {st : Storage C} {r : SRef C (.prim P)}
    {w : SVal (.prim P)} (h : st.find r = some w) :
    st.obs.word (.ref r) = (SVal.view w : P.Denote) := by
  have e := congrArg (fun o : TVal _ => o.word .nil) (Storage.obs_find_some h)
  simp only [Obs.find_word] at e
  rw [show (ObsLoc.app (SLoc.ref r) .nil : SLoc C _) = .ref r from congrArg SLoc.ref
    (SRef.append_nil r)] at e
  rw [e]
  cases w; rfl

/-- A push that returns had room. -/
theorem Storage.full_of_push {C : Contract} {E : Ty} {st st' : Storage C}
    {r : SRef C (.ref (.array E))} {val : SVal E → Option (SVal E)}
    (h : st.push r val = some st') : st.full r = false := by
  unfold Storage.push at h
  unfold Storage.full
  cases hf : st.find r with
  | none => rfl
  | some v =>
    simp only [hf, Option.bind_eq_bind, Option.bind_some] at h
    by_cases hb : (SVal.view v : ArrView E).n + 1 < 2 ^ 256
    · simp only [hb, decide_true, Bool.not_true]
    · exfalso
      revert h
      cases val (pushSlot E (SVal.view v : ArrView E).shadow.toList).1 <;>
        simp only [Option.bind_none, Option.bind_some, hb, dite_false, reduceCtorEq,
          imp_self]

/-- A push as a place that returns had room. -/
theorem Storage.full_of_pushPlace {C : Contract} {E : Ty} {st : Storage C}
    {r : SRef C (.ref (.array E))} {q : Storage C × Nat}
    (h : st.pushPlace r = some q) : st.full r = false := by
  unfold Storage.pushPlace at h
  unfold Storage.full
  cases hf : st.find r with
  | none => rfl
  | some v =>
    simp only [hf, Option.bind_eq_bind, Option.bind_some] at h
    by_cases hb : (SVal.view v : ArrView E).n + 1 < 2 ^ 256
    · simp only [hb, decide_true, Bool.not_true]
    · simp only [hb, dite_false, reduceCtorEq] at h

theorem Op0.denote_eval {s : Srt} (o : Op0 C s) : Srt.BridgeO C g.H s (o.denote g) (o.eval g) := by
  intro v hv
  rw [Op0.eval_eq_evalM] at hv
  cases o <;> simp only [Op0.evalM, Option.some.injEq] at hv <;> subst hv
  all_goals first | rfl | trivial

theorem Op1.denote_eval {a s : Srt} (o : Op1 C a s) {x : Option (a.Den C g.H)} {d : a.TDen C}
    (hx : Srt.BridgeO C g.H a d x) : Srt.BridgeO C g.H s (o.denote g d) (o.eval g x) := by
  intro v hv
  rw [Op1.eval_eq_evalM] at hv
  cases x with
  | none => cases o <;> simp only [Op1.evalM, Option.bind_none, Option.map_none, reduceCtorEq] at hv
  | some u =>
  have hu := hx u rfl
  cases o with
  | unop op h =>
    simp only [Srt.Bridge] at hu ⊢
    simp only [Op1.evalM] at hv
    rw [Op1.denote, hu]; exact hv
  | net | delValue | toInt =>
    simp only [Srt.Bridge] at hu ⊢
    simp only [Op1.evalM] at hv
    rw [Op1.denote, hu]; exact hv
  | field h | fieldIn h =>
    simp only [Op1.evalM, Option.map_some, Option.some.injEq] at hv
    subst hv
    simp only [Srt.Bridge] at hu ⊢
    rw [Op1.denote, hu]; rfl
  | next =>
    simp only [Op1.evalM, Option.bind_some, Storage.nextT, Option.map_eq_some_iff] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    simp only [Srt.Bridge] at hu ⊢
    rw [Op1.denote, hu, Storage.obs_len_ref_some hw, SRef.index, Path.index_dyn]
    rfl
  | sval =>
    simp only [Op1.evalM, Option.map_some, Option.some.injEq] at hv
    subst hv
    simp only [Srt.Bridge] at hu ⊢
    rw [Op1.denote, hu]; rfl
  | newArr h =>
    simp only [Op1.evalM, Option.map_some, Option.some.injEq] at hv
    subst hv
    simp only [Srt.Bridge] at hu ⊢
    rw [Op1.denote, hu]; rfl
  | alloc | mfield | addM | mval | ref => trivial
  | wt =>
    simp only [Op1.evalM, Option.bind_some, Storage.wtT] at hv
    split at hv
    · cases hv; rfl
    · cases hv
  | select r h =>
    simp only [Op1.evalM, Option.map_some, Option.some.injEq] at hv
    subst hv
    simp only [Srt.Bridge] at hu ⊢
    rw [Op1.denote, hu, Storage.obs_selectT]
  | selectIn h =>
    simp only [Op1.evalM, Option.map_some, Option.some.injEq] at hv
    subst hv
    simp only [Srt.Bridge] at hu ⊢
    rw [Op1.denote, hu, Storage.obs_selectT]

theorem Op2.denote_eval {a b s : Srt} (o : Op2 C a b s) {x : Option (a.Den C g.H)}
    {y : Option (b.Den C g.H)} {da : a.TDen C} {db : b.TDen C}
    (hx : Srt.BridgeO C g.H a da x) (hy : Srt.BridgeO C g.H b db y) :
    Srt.BridgeO C g.H s (o.denote g x y da db) (o.eval g x y) := by
  intro v hv
  have hv' := hv
  rw [Op2.eval_eq_evalM] at hv
  cases x with
  | none => cases o <;> simp only [Op2.evalM, Option.bind_none, Option.bind_eq_bind,
      reduceCtorEq] at hv
  | some u =>
  have hu := hx u rfl
  cases o with
  | binop op h =>
    simp only [Op2.evalM, Option.bind_some] at hv
    simp only [Srt.Bridge] at hu ⊢
    rw [Op2.denote, hu, Option.bind_some]
    unfold binopT at hv ⊢
    cases hs : op.shortT u with
    | some r => rw [hs] at hv; exact hv
    | none =>
      rw [hs] at hv
      cases y with
      | none => cases hv
      | some w =>
        have hw : db = some w := hy w rfl
        rw [hw]; exact hv
  | read | mlen => exact hv'
  | copyMem =>
    simp only [Srt.Bridge]
    rw [Op2.denote, hv']
  | iread | copy | mat | copySt => trivial
  | _ =>
    cases y with
    | none => simp only [Op2.evalM, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
        reduceCtorEq] at hv
    | some w =>
    have hw := hy w rfl
    simp only [Srt.Bridge] at hu hw ⊢
    try simp only [Op2.evalM, Option.bind_some, Option.bind_eq_bind] at hv
    subst hu hw
    all_goals first
    | (rw [Op2.denote]
       simp only [Option.bind_eq_some_iff, Option.some.injEq] at hv
       obtain ⟨w', hw', rfl⟩ := hv
       rw [Storage.obs_word_ref_some hw'])
    | (rw [Op2.denote]
       simp only [Storage.len, Option.bind_eq_bind, Option.bind_eq_some_iff,
         Option.some.injEq] at hv
       obtain ⟨w', hw', rfl⟩ := hv
       rw [Storage.obs_len_ref_some hw', lenW, dif_pos])
    | (simp only [Storage.atT, Option.bind_eq_bind, Option.bind_eq_some_iff,
         Option.some.injEq] at hv
       obtain ⟨_, _, rfl⟩ := hv
       rfl)
    | (simp only [Storage.nextT, Option.map_eq_some_iff] at hv
       obtain ⟨w', hw', rfl⟩ := hv
       rw [Op2.denote, Storage.obs_len_ref_some hw', SRef.index, Path.index_dyn]
       rfl)
    | (rw [Op2.denote, Storage.obs_delete hv])
    | (rw [Op2.denote, Storage.obs_push_slot hv])
    | (rw [Op2.denote, Storage.obs_pop hv])
    | (simp only [Option.bind_eq_some_iff, Option.some.injEq] at hv
       obtain ⟨⟨st', k⟩, hp, rfl⟩ := hv
       rw [Op2.denote, Storage.obs_pushPlace hp])
    | (rw [Op2.denote, Storage.obs_find_some hv])
    | (simp only [Option.some.injEq] at hv
       subst hv
       rfl)

theorem Op3.denote_eval {a b c s : Srt} (o : Op3 C a b c s) {x : Option (a.Den C g.H)}
    {y : Option (b.Den C g.H)} {z : Option (c.Den C g.H)} {da : a.TDen C} {db : b.TDen C}
    {dc : c.TDen C} (hx : Srt.BridgeO C g.H a da x) (hy : Srt.BridgeO C g.H b db y)
    (hz : Srt.BridgeO C g.H c dc z) :
    Srt.BridgeO C g.H s (o.denote da db dc) (o.eval g x y z) := by
  intro v hv
  rw [Op3.eval_eq_evalM] at hv
  cases x with
  | none => cases o <;> simp only [Op3.evalM, Option.bind_none, Option.bind_eq_bind,
      reduceCtorEq] at hv
  | some u =>
  have hu := hx u rfl
  cases o with
  | ite =>
    simp only [Op3.evalM, Option.bind_some] at hv
    simp only [Srt.Bridge] at hu
    rw [Op3.denote, hu, Option.bind_some]
    cases u with
    | true => exact hy v hv
    | false => exact hz v hv
  | write => trivial
  | _ =>
    cases y with
    | none => simp only [Op3.evalM, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
        reduceCtorEq] at hv
    | some w =>
    cases z with
    | none => simp only [Op3.evalM, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
        Option.map_none, Storage.push_none, reduceCtorEq] at hv
    | some t =>
    have hw := hy w rfl
    have ht := hz t rfl
    simp only [Srt.Bridge] at hu hw ht ⊢
    simp only [Op3.evalM, Option.bind_some, Option.bind_eq_bind, Option.map_some] at hv
    subst hu hw ht
    first
    | (rw [Op3.denote, Storage.obs_write hv])
    | (simp only [Storage.atT, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at hv
       obtain ⟨_, _, rfl⟩ := hv
       rfl)
    | (rw [Op3.denote, ← SVal.obs_strip, Storage.obs_push hv])

end Bridge

end Solidity
