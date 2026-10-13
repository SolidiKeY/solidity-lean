import Solidity.Calculus.DecideScoped
import Solidity.Calculus.DecideEval

/-!
# The scoped reduction, sound over the typed state

`Fml.toLS` (`Calculus/DecideScoped.lean`) pushes a scoped leaf's updates in
by position.  Its soundness is proved here on the leaf itself, over the
typed state and its run (`holds`, `Calculus/Logic.lean`): the reduction is
read in the state the leaf starts in (`g₀`, its atoms in `ν`), the leaf in
the state its updates reach (`τ`), and what relates them is `Agrees`: the
storage term the updates left reads `τ`'s storage, the memory term `τ`'s
heap, each bound position `τ`'s local (`LTy.vopt`), and the values of the
transaction are `g₀`'s.

* A term pushed in reads what the scoped term reads (`Tm.toL_drel`):
  equal, a memory up to the heap typing it grew from (`Srt.DRel`), since a
  symbol reads its arguments alike in either state, `at` and `next` aside,
  which read the storage they were pushed onto.
* An update pushed in returns exactly where the update does, and the state
  it leaves agrees with every typed state the update lands on
  (`Upd.toLS_sound`, through `Upd.applyV`).
* A formula pushed in implies the formula at the positive polarity and
  follows from it at the negative one (`Fml.toLS_sound`).

`Valid.of_reduceS` puts it together with the elimination
(`LFml.elim_holds`, `Calculus/DecideEval.lean`).
-/

namespace Solidity

namespace Decide

open Semantics

variable {C : Contract}

/-! ## Two readings of a sort -/

/-- A memory, up to the heap typing it grew from: its heap. -/
def _root_.Solidity.Grown.forget {H : HTy} (m : Grown H (fun _ => Unit)) : (H' : HTy) × Heap H' :=
  ⟨m.H', m.heap⟩

theorem _root_.Solidity.Grown.forget_inj {H₁ H₂ : HTy} {m₁ : Grown H₁ (fun _ => Unit)}
    {m₂ : Grown H₂ (fun _ => Unit)} (h : m₁.forget = m₂.forget) :
    ∃ (H' : HTy) (hp : Heap H') (e₁ : H₁ <+: H') (e₂ : H₂ <+: H'),
      m₁ = ⟨e₁, hp, ()⟩ ∧ m₂ = ⟨e₂, hp, ()⟩ := by
  cases m₁ with | mk e₁ hp₁ u₁ =>
  cases m₂ with | mk e₂ hp₂ u₂ =>
  simp only [Grown.forget, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  cases h
  exact ⟨_, _, e₁, e₂, rfl, rfl⟩

/-- **Two readings of a sort agree**, over two heap typings: equal, a
memory by its heap. -/
def _root_.Solidity.Srt.DRel : (s : Srt) → {H₁ H₂ : HTy} → Option (s.Den C H₁) →
    Option (s.Den C H₂) → Prop
  | .mem, _, _, x, y =>
    (x : Option (Grown _ _)).map Grown.forget = (y : Option (Grown _ _)).map Grown.forget
  | .val p, _, _, x, y => (x : Option p.Denote) = y
  | .path T, _, _, x, y => (x : Option (SRef C T)) = y
  | .st, _, _, x, y => (x : Option (Storage C)) = y
  | .sv T, _, _, x, y => (x : Option (SVal T)) = y
  | .ident _, _, _, x, y => (x : Option Nat) = y
  | .addr T, _, _, x, y => (x : Option (MAddrT T)) = y
  | .mv T, _, _, x, y => (x : Option (MvT T)) = y
  | .sts s, _, _, x, y => (x : Option (Storage (Contract.ofStruct s))) = y
  | .spath s T, _, _, x, y => (x : Option (SRef (Contract.ofStruct s) T)) = y
  | .kint, _, _, x, y => (x : Option Int) = y

/-! ## The symbols, read in two states -/

/-- `net`. -/
def _root_.Solidity.Op1.isNet {a s : Srt} : Op1 C a s → Bool
  | .net => true
  | _ => false

/-- `next`. -/
def _root_.Solidity.Op1.isNext {a s : Srt} : Op1 C a s → Bool
  | .next => true
  | _ => false

/-- `storage`. -/
def _root_.Solidity.Op0.isStorage {s : Srt} : Op0 C s → Bool
  | .storage => true
  | _ => false

/-- `memory`. -/
def _root_.Solidity.Op0.isMemory {s : Srt} : Op0 C s → Bool
  | .memory => true
  | _ => false

/-- `at`. -/
def _root_.Solidity.Op2.isAt {a b s : Srt} : Op2 C a b s → Bool
  | .at _ => true
  | _ => false

section Ops

variable (g₁ g₂ : State C [])

theorem Op1.eval_drel {a s : Srt} (o : Op1 C a s) (hnet : o.isNet = false)
    (hnext : o.isNext = false)
    {x₁ : Option (a.Den C g₁.H)} {x₂ : Option (a.Den C g₂.H)} (hx : Srt.DRel a x₁ x₂) :
    Srt.DRel s (o.eval g₁ x₁) (o.eval g₂ x₂) := by
  cases o with
  | net => cases hnet
  | next => cases hnext
  | alloc R h =>
    cases x₁ <;> cases x₂ <;> simp only [Srt.DRel, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at hx
    · rfl
    · obtain ⟨H', hp, e₁, e₂, rfl, rfl⟩ := Grown.forget_inj hx
      rfl
  | addM R h =>
    cases x₁ <;> cases x₂ <;> simp only [Srt.DRel, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at hx
    · rfl
    · obtain ⟨H', hp, e₁, e₂, rfl, rfl⟩ := Grown.forget_inj hx
      rfl
  | _ => cases hx; rfl

theorem Op2.eval_drel {a b s : Srt} (o : Op2 C a b s) (hat : o.isAt = false)
    {x₁ : Option (a.Den C g₁.H)} {x₂ : Option (a.Den C g₂.H)} (hx : Srt.DRel a x₁ x₂)
    {y₁ : Option (b.Den C g₁.H)} {y₂ : Option (b.Den C g₂.H)} (hy : Srt.DRel b y₁ y₂) :
    Srt.DRel s (o.eval g₁ x₁ y₁) (o.eval g₂ x₂ y₂) := by
  cases o with
  | «at» it => cases hat
  | read | mlen | copyMem | iread | copy =>
    cases x₁ <;> cases x₂ <;> simp only [Srt.DRel, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at hx
    · cases hy; rfl
    · obtain ⟨H', hp, e₁, e₂, rfl, rfl⟩ := Grown.forget_inj hx
      cases hy; rfl
  | copySt h =>
    cases x₁ <;> cases x₂ <;> simp only [Srt.DRel, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at hx
    · cases hy; rfl
    · obtain ⟨H', hp, e₁, e₂, rfl, rfl⟩ := Grown.forget_inj hx
      cases hy
      cases y₁ <;> rfl
  | _ => cases hx; cases hy; rfl

theorem writeT_forget {H₁ H₂ H' : HTy} {T : Ty} (e₁ : H₁ <+: H') (e₂ : H₂ <+: H') (hp : Heap H')
    (a : MAddrT T) (v : MvT T) :
    (Grown.writeT (⟨e₁, hp, ()⟩ : Grown H₁ (fun _ => Unit)) a v).map Grown.forget =
      (Grown.writeT (⟨e₂, hp, ()⟩ : Grown H₂ (fun _ => Unit)) a v).map Grown.forget := by
  simp only [Grown.writeT, Option.bind_eq_bind]
  cases MAddrT.resolve H' a <;> simp only [Option.bind_none, Option.bind_some, Option.map_none]
  rename_i ad
  cases MvT.toMVal H' T v <;> simp only [Option.bind_none, Option.bind_some, Option.map_none]
  rename_i mv
  cases hp.writeAddr ad mv <;> rfl

theorem Op3.eval_drel {a b c s : Srt} (o : Op3 C a b c s)
    {x₁ : Option (a.Den C g₁.H)} {x₂ : Option (a.Den C g₂.H)} (hx : Srt.DRel a x₁ x₂)
    {y₁ : Option (b.Den C g₁.H)} {y₂ : Option (b.Den C g₂.H)} (hy : Srt.DRel b y₁ y₂)
    {z₁ : Option (c.Den C g₁.H)} {z₂ : Option (c.Den C g₂.H)} (hz : Srt.DRel c z₁ z₂) :
    Srt.DRel s (o.eval g₁ x₁ y₁ z₁) (o.eval g₂ x₂ y₂ z₂) := by
  cases o with
  | write =>
    cases x₁ <;> cases x₂ <;> simp only [Srt.DRel, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at hx
    · cases hy; cases hz; rfl
    · obtain ⟨H', hp, e₁, e₂, rfl, rfl⟩ := Grown.forget_inj hx
      cases hy; cases hz
      cases y₁ <;> cases z₁ <;> try rfl
      rename_i a v
      exact writeT_forget e₁ e₂ hp a v
  | _ => cases hx; cases hy; cases hz; rfl

theorem Op0.eval_drel {s : Srt} (o : Op0 C s) (hs : o.isStorage = false) (hm : o.isMemory = false)
    (htx : g₁.tx = g₂.tx) (hbal : g₁.selfBalance = g₂.selfBalance) :
    Srt.DRel s (o.eval g₁) (o.eval g₂) := by
  cases o with
  | storage => cases hs
  | memory => cases hm
  | env k =>
    show some (g₁.envVal k) = some (g₂.envVal k)
    cases k <;> simp only [State.envVal, htx, hbal]
  | _ => rfl

end Ops

/-! ## The relation -/

/-- What a position bound to a term reads: its local's value, at the sort
it is bound at. -/
def _root_.Solidity.LTy.vopt {H : HTy} : (t : LTy) → t.VDen C → Option (t.bs.Den C H)
  | .val _, v => some v
  | .alias _, v => v
  | .mem _, v => v
  | .old, v => some v
  | .oldNet, _ => none
  | .kint, v => some v

/-- A term is fresh from the position `n` on: binding an atom there leaves
what it reads. -/
def Fresh {s : Srt} (n : Nat) (t : LTm C s) : Prop :=
  ∀ (g : State C []) (ν : AEnv) (p : PrimTy) (k : Nat) (v : p.Denote), n ≤ k →
    t.eval g (ν.set p k v) = t.eval g ν

/-- Every binding fresh from `n` on. -/
def BEnv.Fresh (n : Nat) : {Γ : Ctx} → BEnv C Γ → Prop
  | [], _ => True
  | _ :: _, e => (∀ b, e.1 = some b → Decide.Fresh n b) ∧ BEnv.Fresh n e.2

/-- The symbolic state is fresh past its next position. -/
structure SymS.Fresh {Γ : Ctx} (ρ : SymS C Γ) : Prop where
  stor : Decide.Fresh ρ.next ρ.stor
  mem : Decide.Fresh ρ.next ρ.mem
  loc : ρ.loc.Fresh ρ.next

/-- **The reduction's state `ρ`, read in `g₀` and `ν`, stands for the
global part `G` and the locals `ℓ`.** -/
structure AgreesV (g₀ : State C []) (ν : AEnv) {Γ : Ctx} (ρ : SymS C Γ) (G : State C [])
    (ℓ : LocsV C Γ) : Prop where
  stor : (ρ.stor.eval g₀ ν : Option (Storage C)) = some G.storage
  mem : (ρ.mem.eval g₀ ν : Option (Grown g₀.H (fun _ => Unit))).map Grown.forget =
    some ⟨G.H, G.heap⟩
  tx : g₀.tx = G.tx
  bal : g₀.selfBalance = G.selfBalance
  loc : ∀ {t : LTy} (i : Idx Γ t) (b : LTm C t.bs), ρ.loc.get i = some b →
    (b.eval g₀ ν : Option (t.bs.Den C g₀.H)) = t.vopt (ℓ t i)

/-- At a typed state: its global part and its locals. -/
abbrev Agrees (g₀ : State C []) (ν : AEnv) {Γ : Ctx} (ρ : SymS C Γ) (τ : State C Γ) : Prop :=
  AgreesV g₀ ν ρ τ.glob τ.locV

/-! ## Terms, by position -/

section Terms

variable {g₀ : State C []} {ν : AEnv} {Γ : Ctx} {ρ : SymS C Γ} {τ : State C Γ}

theorem Op0.toL_ne {s : Srt} (o : Op0 C s) (hs : o.isStorage = false) (hm : o.isMemory = false) :
    o.toL ρ = some (.app0 o) := by
  cases o <;> simp only [Op0.isStorage, Op0.isMemory, reduceCtorEq] at hs hm <;> rfl

theorem Op1.toL_ne {a s : Srt} (o : Op1 C a s) (x : LTm C a) (hnet : o.isNet = false)
    (hnext : o.isNext = false) : o.toL ρ x = some (.app1 o x) := by
  cases o <;> simp only [Op1.isNet, Op1.isNext, reduceCtorEq] at hnet hnext <;> rfl

theorem Op2.toL_ne {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b)
    (hat : o.isAt = false) : o.toL ρ x y = some (.app2 o x y) := by
  cases o <;> simp only [Op2.isAt, reduceCtorEq] at hat <;> rfl

/-- **A term pushed in reads what the scoped term reads.** -/
theorem Tm.toL_drel (h : Agrees g₀ ν ρ τ) :
    {s : Srt} → (t : Tm C Γ s) → (t' : LTm C s) → t.toL ρ = some t' →
      Srt.DRel s (t'.eval g₀ ν) (t.eval τ)
  | _, .pvV i, t', ht => by
    have := h.loc i t' ht; rw [this]; rfl
  | _, .pvP i, t', ht => by
    have := h.loc i t' ht; rw [this]; rfl
  | _, .pvS i, t', ht => by
    have := h.loc i t' ht; rw [this]; rfl
  | _, .pvI i, t', ht => by
    have := h.loc i t' ht; rw [this]; rfl
  | _, .pvZ i, t', ht => by
    have := h.loc i t' ht; rw [this]; rfl
  | _, .netOf _ _, t', ht => by cases ht
  | _, .app0 o, t', ht => by
    cases o with
    | storage =>
      cases ht
      show (ρ.stor.eval g₀ ν : Option (Storage C)) = some τ.storage
      exact h.stor
    | memory =>
      cases ht
      exact h.mem
    | lit v => cases ht; exact Op0.eval_drel g₀ τ.glob (.lit v) rfl rfl h.tx h.bal
    | env k => cases ht; exact Op0.eval_drel g₀ τ.glob (.env k) rfl rfl h.tx h.bal
    | root r hr => cases ht; exact Op0.eval_drel g₀ τ.glob (.root r hr) rfl rfl h.tx h.bal
    | mtSt => cases ht; exact Op0.eval_drel g₀ τ.glob .mtSt rfl rfl h.tx h.bal
    | member s f hf => cases ht; exact Op0.eval_drel g₀ τ.glob (.member s f hf) rfl rfl h.tx h.bal
    | zlit n => cases ht; exact Op0.eval_drel g₀ τ.glob (.zlit n) rfl rfl h.tx h.bal
  | _, .app1 o x, t', ht => by
    simp only [Tm.toL, Option.bind_eq_some_iff] at ht
    obtain ⟨x', hx', ht⟩ := ht
    have hx := Tm.toL_drel h x x' hx'
    cases hn : o.isNet with
    | true => cases o <;> simp only [Op1.isNet, reduceCtorEq] at hn; cases ht
    | false =>
      cases hm : o.isNext with
      | true =>
        cases o <;> simp only [Op1.isNext, reduceCtorEq] at hm
        cases ht
        rw [LTm.eval_app2, Tm.eval_app1, h.stor]
        show (Option.bind _ _ : Option _) = Option.bind _ _
        rw [show (x'.eval g₀ ν : Option (SRef C _)) = x.eval τ from hx]
      | false =>
        rw [Op1.toL_ne o x' hn hm] at ht
        cases ht
        exact Op1.eval_drel g₀ τ.glob o hn hm hx
  | _, .app2 o x y, t', ht => by
    simp only [Tm.toL, Option.bind_eq_some_iff] at ht
    obtain ⟨x', hx', y', hy', ht⟩ := ht
    have hx := Tm.toL_drel h x x' hx'
    have hy := Tm.toL_drel h y y' hy'
    cases ha : o.isAt with
    | true =>
      cases o <;> simp only [Op2.isAt, reduceCtorEq] at ha
      cases ht
      rw [LTm.eval_app3, Tm.eval_app2, h.stor]
      rw [show (x'.eval g₀ ν : Option (SRef C _)) = x.eval τ from hx,
        show (y'.eval g₀ ν : Option _) = y.eval τ from hy]
      rfl
    | false =>
      rw [Op2.toL_ne o x' y' ha] at ht
      cases ht
      exact Op2.eval_drel g₀ τ.glob o ha hx hy
  | _, .app3 o x y z, t', ht => by
    simp only [Tm.toL, Option.bind_eq_some_iff] at ht
    obtain ⟨x', hx', y', hy', z', hz', ht⟩ := ht
    cases ht
    exact Op3.eval_drel g₀ τ.glob o (Tm.toL_drel h x x' hx') (Tm.toL_drel h y y' hy')
      (Tm.toL_drel h z z' hz')

end Terms

/-! ## The bindings, by position -/

namespace BEnv

theorem get_set_same : {Γ : Ctx} → {t : LTy} → (i : Idx Γ t) → (w : Option (LTm C t.bs)) →
    (e : BEnv C Γ) → BEnv.get i (BEnv.set i w e) = w
  | _, _, .here, _, _ => rfl
  | _, _, .there i, w, e => get_set_same i w e.2

theorem get_set_ne : {Γ : Ctx} → {t u : LTy} → (i : Idx Γ t) → (j : Idx Γ u) →
    i.toNat ≠ j.toNat → (w : Option (LTm C t.bs)) → (e : BEnv C Γ) →
    BEnv.get j (BEnv.set i w e) = BEnv.get j e
  | _, _, _, .here, .here, h, _, _ => absurd rfl h
  | _, _, _, .here, .there _, _, _, _ => rfl
  | _, _, _, .there _, .here, _, _, _ => rfl
  | _, _, _, .there i, .there j, h, w, e =>
    get_set_ne i j (fun h' => h (congrArg (· + 1) h')) w e.2

theorem get_drop {Γ : Ctx} {t : LTy} (i : Idx Γ t) : {Δ : Ctx} → (h : Ext Γ Δ) → (e : BEnv C Δ) →
    BEnv.get i (BEnv.drop h e) = BEnv.get (i.ext h) e
  | _, .refl, _ => rfl
  | _, .push h, e => get_drop i h e.2

theorem get_thin : {Γ Δ : Ctx} → (h : Thin Γ Δ) → {t : LTy} → (i : Idx Γ t) → (e : BEnv C Δ) →
    BEnv.get i (BEnv.thin h e) = BEnv.get (i.wk h) e
  | _, _, .refl, _, _, _ => rfl
  | _, _, .keep _, _, .here, _ => rfl
  | _, _, .keep h, _, .there i, e => get_thin h i e.2
  | _, _, .drop h, _, i, e => get_thin h i e.2

theorem Fresh.get {n : Nat} : {Γ : Ctx} → {e : BEnv C Γ} → BEnv.Fresh n e → {t : LTy} →
    (i : Idx Γ t) → (b : LTm C t.bs) → BEnv.get i e = some b → Decide.Fresh n b
  | _ :: _, _, h, _, .here, b, hb => h.1 b hb
  | _ :: _, _, h, _, .there i, b, hb => Fresh.get h.2 i b hb

theorem Fresh.mono {n m : Nat} (hnm : n ≤ m) : {Γ : Ctx} → {e : BEnv C Γ} → BEnv.Fresh n e →
    BEnv.Fresh m e
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨fun b hb g ν p k v hk => h.1 b hb g ν p k v (Nat.le_trans hnm hk),
      Fresh.mono hnm h.2⟩

theorem Fresh.set {n : Nat} : {Γ : Ctx} → {t : LTy} → (i : Idx Γ t) → {w : Option (LTm C t.bs)} →
    (∀ b, w = some b → Decide.Fresh n b) → {e : BEnv C Γ} → BEnv.Fresh n e →
    BEnv.Fresh n (BEnv.set i w e)
  | _, _, .here, _, hw, _, h => ⟨hw, h.2⟩
  | _, _, .there i, _, hw, _, h => ⟨h.1, Fresh.set i hw h.2⟩

theorem Fresh.drop {n : Nat} {Γ : Ctx} : {Δ : Ctx} → (h : Ext Γ Δ) → {e : BEnv C Δ} →
    BEnv.Fresh n e → BEnv.Fresh n (BEnv.drop h e)
  | _, .refl, _, hf => hf
  | _, .push h, _, hf => Fresh.drop h hf.2

theorem Fresh.thin {n : Nat} : {Γ Δ : Ctx} → (h : Thin Γ Δ) → {e : BEnv C Δ} →
    BEnv.Fresh n e → BEnv.Fresh n (BEnv.thin h e)
  | _, _, .refl, _, hf => hf
  | _, _, .keep h, _, hf => ⟨hf.1, Fresh.thin h hf.2⟩
  | _, _, .drop h, _, hf => Fresh.thin h hf.2

end BEnv

theorem Fresh.mono {s : Srt} {n m : Nat} (hnm : n ≤ m) {t : LTm C s} (h : Fresh n t) : Fresh m t :=
  fun g ν p k v hk => h g ν p k v (Nat.le_trans hnm hk)

/-! ## Freshness of the terms pushed in -/

section FreshTerms

variable {Γ : Ctx} {ρ : SymS C Γ}

theorem Fresh.app0 {s : Srt} (n : Nat) (o : Op0 C s) : Fresh n (LTm.app0 o) := fun _ _ _ _ _ _ => rfl

theorem Fresh.app1 {a s : Srt} {n : Nat} (o : Op1 C a s) {x : LTm C a} (hx : Fresh n x) :
    Fresh n (LTm.app1 o x) := fun g ν p k v hk => by
  rw [LTm.eval_app1, LTm.eval_app1, hx g ν p k v hk]

theorem Fresh.app2 {a b s : Srt} {n : Nat} (o : Op2 C a b s) {x : LTm C a} {y : LTm C b}
    (hx : Fresh n x) (hy : Fresh n y) : Fresh n (LTm.app2 o x y) := fun g ν p k v hk => by
  rw [LTm.eval_app2, LTm.eval_app2, hx g ν p k v hk, hy g ν p k v hk]

theorem Fresh.app3 {a b c s : Srt} {n : Nat} (o : Op3 C a b c s) {x : LTm C a} {y : LTm C b}
    {z : LTm C c} (hx : Fresh n x) (hy : Fresh n y) (hz : Fresh n z) :
    Fresh n (LTm.app3 o x y z) := fun g ν p k v hk => by
  rw [LTm.eval_app3, LTm.eval_app3, hx g ν p k v hk, hy g ν p k v hk, hz g ν p k v hk]

theorem Fresh.err {s : Srt} (n : Nat) : Fresh n (LTm.err : LTm C s) := fun _ _ _ _ _ _ => rfl

theorem Fresh.seqL {s' s : Srt} {n : Nat} {d : LTm C s'} {a : LTm C s} (hd : Fresh n d)
    (ha : Fresh n a) : Fresh n (seqL d a) := fun g ν p k v hk => by
  rw [seqL_eval, seqL_eval, hd g ν p k v hk, ha g ν p k v hk]

theorem Fresh.tt (n : Nat) : Fresh n (LTm.tt : LTm C (.val .bool)) := Fresh.app0 n _

/-- **A term pushed in is fresh where the state is.** -/
theorem Tm.toL_fresh (hF : ρ.Fresh) : {s : Srt} → (t : Tm C Γ s) → (t' : LTm C s) →
    t.toL ρ = some t' → Fresh ρ.next t'
  | _, .pvV i, t', ht | _, .pvP i, t', ht | _, .pvS i, t', ht | _, .pvI i, t', ht
  | _, .pvZ i, t', ht => hF.loc.get i t' ht
  | _, .netOf _ _, _, ht => by cases ht
  | _, .app0 o, t', ht => by
    cases o <;> cases ht <;> first | exact hF.stor | exact hF.mem | exact Fresh.app0 _ _
  | _, .app1 o x, t', ht => by
    simp only [Tm.toL, Option.bind_eq_some_iff] at ht
    obtain ⟨x', hx', ht⟩ := ht
    have hx := Tm.toL_fresh hF x x' hx'
    cases o <;> cases ht <;> first | exact Fresh.app1 _ hx | exact Fresh.app2 _ hF.stor hx
  | _, .app2 o x y, t', ht => by
    simp only [Tm.toL, Option.bind_eq_some_iff] at ht
    obtain ⟨x', hx', y', hy', ht⟩ := ht
    have hx := Tm.toL_fresh hF x x' hx'
    have hy := Tm.toL_fresh hF y y' hy'
    cases o <;> cases ht <;> first | exact Fresh.app2 _ hx hy | exact Fresh.app3 _ hF.stor hx hy
  | _, .app3 o x y z, t', ht => by
    simp only [Tm.toL, Option.bind_eq_some_iff] at ht
    obtain ⟨x', hx', y', hy', z', hz', ht⟩ := ht
    cases ht
    exact Fresh.app3 _ (Tm.toL_fresh hF x x' hx') (Tm.toL_fresh hF y y' hy')
      (Tm.toL_fresh hF z z' hz')

end FreshTerms

/-! ## Updates, by position -/

section Upd

variable {g₀ : State C []} {ν : AEnv} {Γ : Ctx} {ρ₀ : SymS C Γ} {τ : State C Γ}

theorem seqL_tt_drel {s : Srt} {x : LTm C s} {y : Option (s.Den C τ.H)} (h : Srt.DRel s (x.eval g₀ ν) y) :
    ((seqL x .tt).eval g₀ ν : Option Bool) = y.map fun _ => true := by
  rw [seqL_tt_eval]
  cases s <;> first
    | (cases h; rfl)
    | (cases hx : x.eval g₀ ν <;> cases hy : y <;> rw [hx, hy] at h <;>
        simp only [Srt.DRel, Option.map_none, Option.map_some, reduceCtorEq] at h <;> rfl)

/-- **A right-hand side pushed in**: its guard returns where it does, and
its binding reads what it sets the local to. -/
theorem Rhs.toL_sound (hA : Agrees g₀ ν ρ₀ τ) (hF : ρ₀.Fresh) {t : LTy} (r : Rhs C Γ t)
    {b : LTm C t.bs} {gd : LTm C (.val .bool)} (h : r.toL ρ₀ = some (b, gd)) :
    (gd.eval g₀ ν : Option Bool) = (r.eval τ).map (fun _ => true) ∧
      (∀ v, r.eval τ = some v → (b.eval g₀ ν : Option (t.bs.Den C g₀.H)) = t.vopt v) ∧
      Fresh ρ₀.next b := by
  cases r with
  | val x =>
    simp only [Rhs.toL, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨x', hx', rfl, rfl⟩ := h
    have hd := Tm.toL_drel hA x x' hx'
    refine ⟨seqL_tt_drel hd, fun v hv => ?_, Tm.toL_fresh hF x x' hx'⟩
    show (x'.eval g₀ ν : Option _) = some v
    rw [show (x'.eval g₀ ν : Option _) = x.eval τ from hd]; exact hv
  | path q =>
    simp only [Rhs.toL, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨q', hq', rfl, rfl⟩ := h
    have hd := Tm.toL_drel hA q q' hq'
    refine ⟨?_, fun v hv => ?_, Tm.toL_fresh hF q q' hq'⟩
    · rw [seqL_tt_drel hd]
      show _ = Option.map _ (Option.bind _ _)
      cases (q.eval τ : Option (SRef C _)) <;> rfl
    · show (q'.eval g₀ ν : Option _) = v
      rw [show (q'.eval g₀ ν : Option (SRef C _)) = q.eval τ from hd]
      show _ = v
      revert hv
      show Option.bind _ _ = _ → _
      cases (q.eval τ : Option (SRef C _)) <;> intro hv <;> cases hv <;> rfl
  | unset =>
    simp only [Rhs.toL, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun v hv => by cases hv; rfl, Fresh.err _⟩
  | mref i =>
    simp only [Rhs.toL, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨i', hi', rfl, rfl⟩ := h
    have hd := Tm.toL_drel hA i i' hi'
    refine ⟨?_, fun v hv => ?_, Tm.toL_fresh hF i i' hi'⟩
    · rw [seqL_tt_drel hd]
      show _ = Option.map _ (Option.bind _ _)
      cases (i.eval τ : Option Nat) <;> rfl
    · show (i'.eval g₀ ν : Option Nat) = v
      rw [show (i'.eval g₀ ν : Option Nat) = i.eval τ from hd]
      revert hv
      show Option.bind _ _ = _ → _
      cases (i.eval τ : Option Nat) <;> intro hv <;> cases hv <;> rfl
  | store st =>
    simp only [Rhs.toL, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨s', hs', rfl, rfl⟩ := h
    have hd := Tm.toL_drel hA st s' hs'
    refine ⟨?_, fun v hv => ?_, Tm.toL_fresh hF st s' hs'⟩
    · rw [seqL_tt_drel hd]
      show _ = Option.map _ (Option.bind _ _)
      cases (st.eval τ : Option (Storage C)) <;> rfl
    · show (s'.eval g₀ ν : Option (Storage C)) = some v
      rw [show (s'.eval g₀ ν : Option (Storage C)) = st.eval τ from hd]
      revert hv
      show Option.bind _ _ = _ → _
      cases (st.eval τ : Option (Storage C)) <;> intro hv <;> cases hv <;> rfl
  | saveNet => cases h
  | saveNetMt => cases h
  | zint x =>
    simp only [Rhs.toL, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨x', hx', rfl, rfl⟩ := h
    have hd := Tm.toL_drel hA x x' hx'
    refine ⟨seqL_tt_drel hd, fun v hv => ?_, Tm.toL_fresh hF x x' hx'⟩
    show (x'.eval g₀ ν : Option Int) = some v
    rw [show (x'.eval g₀ ν : Option Int) = x.eval τ from hd]; exact hv

theorem AgreesV.setLoc {Δ : Ctx} {ρ : SymS C Δ} {G : State C []} {ℓ : LocsV C Δ}
    (h : AgreesV g₀ ν ρ G ℓ) {t : LTy} (i : Idx Δ t) {b : LTm C t.bs} {v : t.VDen C}
    (hb : (b.eval g₀ ν : Option (t.bs.Den C g₀.H)) = t.vopt v) :
    AgreesV g₀ ν ⟨ρ.loc.set i (some b), ρ.stor, ρ.mem, ρ.next⟩ G (ℓ.set i v) := by
  refine ⟨h.stor, h.mem, h.tx, h.bal, fun {u} j b' hj => ?_⟩
  by_cases e : i.toNat = j.toNat
  · obtain rfl := Idx.ty_eq_of_toNat e
    obtain rfl := Idx.toNat_inj i j e
    simp only [BEnv.get_set_same, Option.some.injEq] at hj
    subst hj
    rw [hb, LocsV.set_same]
  · rw [BEnv.get_set_ne i j e] at hj
    rw [h.loc j b' hj, LocsV.set_ne _ i j e]

/-- **An element pushed in**, read in `ρ₀` and applied to `ρ`: its guard
returns where the element does, and the state it leaves agrees with what
the element leaves. -/
theorem UpdElem.toLS_sound (hA : Agrees g₀ ν ρ₀ τ) (hF0 : ρ₀.Fresh) {Δ : Ctx} (e : UpdElem C Γ Δ)
    {ρ ρ'' : SymS C Δ} {gde : LTm C (.val .bool)} (h : e.toLS ρ₀ ρ = some (ρ'', gde))
    {G : GlobT C τ.H} {ℓ : LocsV C Δ} (hρ : AgreesV g₀ ν ρ G.1 ℓ) (hFρ : ρ.Fresh)
    (hn : ρ₀.next ≤ ρ.next) :
    (gde.eval g₀ ν : Option Bool) = (e.applyV τ G ℓ).map (fun _ => true) ∧
      (∀ q, e.applyV τ G ℓ = some q → AgreesV g₀ ν ρ'' q.1.1 q.2) ∧ ρ''.Fresh ∧
      ρ''.next = ρ.next := by
  cases e with
  | «local» i r =>
    simp only [UpdElem.toLS, Option.map_eq_some_iff] at h
    obtain ⟨⟨b, gd⟩, hr, h⟩ := h
    cases h
    obtain ⟨hg, hv, hfb⟩ := Rhs.toL_sound hA hF0 r hr
    refine ⟨?_, ?_, ⟨hFρ.stor, hFρ.mem, BEnv.Fresh.set i (fun b' hb' => by
      cases hb'; exact hfb.mono hn) hFρ.loc⟩, rfl⟩
    · rw [hg]
      show _ = Option.map _ (Option.bind _ _)
      cases r.eval τ <;> rfl
    · intro q hq
      show AgreesV _ _ _ _ _
      have hq' : (r.eval τ).bind (fun v => some (G, ℓ.set i v)) = some q := hq
      rw [Option.bind_eq_some_iff] at hq'
      obtain ⟨v, hrv, hq''⟩ := hq'
      cases hq''
      exact hρ.setLoc i (hv v hrv)
  | storage st =>
    simp only [UpdElem.toLS, Option.map_eq_some_iff] at h
    obtain ⟨s', hs', h⟩ := h
    cases h
    have hd := Tm.toL_drel hA st s' hs'
    refine ⟨?_, ?_, ⟨(Tm.toL_fresh hF0 st s' hs').mono hn, hFρ.mem, hFρ.loc⟩, rfl⟩
    · rw [seqL_tt_drel hd]
      show _ = Option.map _ (Option.bind (Option.bind _ _) _)
      cases (st.eval τ : Option (Storage C)) <;> rfl
    · intro q hq
      have hq' : ((st.eval τ).bind fun x => some (G.withStorage x)).bind
          (fun g' => some (g', ℓ)) = some q := hq
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hq'
      obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hq'
      exact ⟨by rw [show (s'.eval g₀ ν : Option (Storage C)) = st.eval τ from hd, hx]; rfl,
        hρ.mem, hρ.tx, hρ.bal, hρ.loc⟩
  | memory m =>
    simp only [UpdElem.toLS, Option.map_eq_some_iff] at h
    obtain ⟨m', hm', h⟩ := h
    cases h
    have hd := Tm.toL_drel hA m m' hm'
    refine ⟨?_, ?_, ⟨hFρ.stor, (Tm.toL_fresh hF0 m m' hm').mono hn, hFρ.loc⟩, rfl⟩
    · rw [seqL_tt_drel hd]
      show _ = Option.map _ (Option.bind (Option.bind _ _) _)
      cases (m.eval τ : Option (Grown _ _)) <;> rfl
    · intro q hq
      have hq' : ((m.eval τ).bind fun x => some (G.withMem x)).bind
          (fun g' => some (g', ℓ)) = some q := hq
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hq'
      obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hq'
      refine ⟨hρ.stor, ?_, hρ.tx, hρ.bal, hρ.loc⟩
      have hd' : (m'.eval g₀ ν : Option (Grown g₀.H _)).map Grown.forget =
          (some x : Option (Grown τ.H _)).map Grown.forget := by
        rw [← hx]; exact hd
      exact hd'
  | selfBalance op a => cases h
  | net r op a =>
    simp only [UpdElem.toLS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', a', ha', h⟩ := h
    cases h
    have hdr := Tm.toL_drel hA r r' hr'
    have hda := Tm.toL_drel hA a a' ha'
    refine ⟨?_, ?_, hFρ, rfl⟩
    · rw [seqL_eval, show (r'.eval g₀ ν : Option _) = r.eval τ from hdr]
      show _ = Option.map _ (Option.bind (Option.bind _ _) _)
      cases (r.eval τ : Option PrimTy.uint.Denote)
      · rfl
      · simp only [Option.bind_some]
        rw [seqL_tt_drel hda]
        cases (a.eval τ : Option PrimTy.uint.Denote) <;> rfl
    · intro q hq
      have hq' : (((r.eval τ).bind fun addr => (a.eval τ).bind fun amt => some (G.withNet _)).bind
          (fun g' => some (g', ℓ))) = some q := hq
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hq'
      obtain ⟨_, ⟨_, _, _, _, rfl⟩, rfl⟩ := hq'
      exact ⟨hρ.stor, hρ.mem, hρ.tx, hρ.bal, hρ.loc⟩
  | pay r a =>
    simp only [UpdElem.toLS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', a', ha', h⟩ := h
    cases h
    have hdr := Tm.toL_drel hA r r' hr'
    have hda := Tm.toL_drel hA a a' ha'
    refine ⟨?_, ?_, hFρ, rfl⟩
    · rw [seqL_eval, show (r'.eval g₀ ν : Option _) = r.eval τ from hdr]
      show _ = Option.map _ (Option.bind (Option.bind _ _) _)
      cases (r.eval τ : Option PrimTy.uint.Denote)
      · rfl
      · simp only [Option.bind_some]
        rw [seqL_tt_drel hda]
        cases (a.eval τ : Option PrimTy.uint.Denote) <;> rfl
    · intro q hq
      have hq' : (((r.eval τ).bind fun addr => (a.eval τ).bind fun amt => some (G.withNet _)).bind
          (fun g' => some (g', ℓ))) = some q := hq
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hq'
      obtain ⟨_, ⟨_, _, _, _, rfl⟩, rfl⟩ := hq'
      exact ⟨hρ.stor, hρ.mem, hρ.tx, hρ.bal, hρ.loc⟩
  | netMt r a => cases h
  | setBalance a => cases h

theorem UpdElem.toLS_fresh (hA : Agrees g₀ ν ρ₀ τ) (hF0 : ρ₀.Fresh) {Δ : Ctx} (e : UpdElem C Γ Δ)
    {ρ ρ'' : SymS C Δ} {gde : LTm C (.val .bool)} (h : e.toLS ρ₀ ρ = some (ρ'', gde))
    (hFρ : ρ.Fresh) (hn : ρ₀.next ≤ ρ.next) : ρ''.Fresh ∧ ρ''.next = ρ.next := by
  cases e with
  | «local» i r =>
    simp only [UpdElem.toLS, Option.map_eq_some_iff] at h
    obtain ⟨⟨b, gd⟩, hr, h⟩ := h
    cases h
    obtain ⟨-, -, hfb⟩ := Rhs.toL_sound hA hF0 r hr
    exact ⟨⟨hFρ.stor, hFρ.mem, BEnv.Fresh.set i (fun b' hb' => by
      cases hb'; exact hfb.mono hn) hFρ.loc⟩, rfl⟩
  | storage st =>
    simp only [UpdElem.toLS, Option.map_eq_some_iff] at h
    obtain ⟨s', hs', h⟩ := h
    cases h
    exact ⟨⟨(Tm.toL_fresh hF0 st s' hs').mono hn, hFρ.mem, hFρ.loc⟩, rfl⟩
  | memory m =>
    simp only [UpdElem.toLS, Option.map_eq_some_iff] at h
    obtain ⟨m', hm', h⟩ := h
    cases h
    exact ⟨⟨hFρ.stor, (Tm.toL_fresh hF0 m m' hm').mono hn, hFρ.loc⟩, rfl⟩
  | selfBalance op a => cases h
  | net r op a =>
    simp only [UpdElem.toLS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨r', -, a', -, h⟩ := h
    cases h
    exact ⟨hFρ, rfl⟩
  | pay r a =>
    simp only [UpdElem.toLS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨r', -, a', -, h⟩ := h
    cases h
    exact ⟨hFρ, rfl⟩
  | netMt r a => cases h
  | setBalance a => cases h

/-- **An update pushed in**: its guard returns exactly where the update
returns, and the state it leaves agrees with what the update leaves. -/
theorem Upd.toLS_sound (hA : Agrees g₀ ν ρ₀ τ) (hF0 : ρ₀.Fresh) {Δ : Ctx} (U : Upd C Γ Δ) :
    ∀ {ρ' : SymS C Δ} {gd : LTm C (.val .bool)}, U.toLS ρ₀ = some (ρ', gd) →
    (gd.eval g₀ ν : Option Bool) = (U.applyV τ).map (fun _ => true) ∧
      (∀ q, U.applyV τ = some q → AgreesV g₀ ν ρ' q.1.1 q.2) ∧ ρ'.Fresh ∧ ρ₀.next ≤ ρ'.next := by
  induction U with
  | nil =>
    intro ρ' gd h
    cases h
    refine ⟨rfl, fun q hq => ?_, hF0, Nat.le_refl _⟩
    cases hq
    exact hA
  | snoc U e ih =>
    intro ρ' gd h
    have h' : (U.toLS ρ₀).bind (fun p => (e.toLS ρ₀ p.1).map fun q => (q.1, seqL p.2 q.2)) =
      some (ρ', gd) := h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h'
    obtain ⟨⟨ρ₁, gd₁⟩, hU, ⟨ρ₂, gd₂⟩, he, hp⟩ := h'
    cases hp
    obtain ⟨hg₁, ha₁, hf₁, hn₁⟩ := ih hU
    show (seqL gd₁ gd₂).eval g₀ ν = Option.map _ ((U.applyV τ).bind _) ∧ _
    rw [seqL_eval, hg₁]
    cases hq : U.applyV τ with
    | none =>
      refine ⟨rfl, fun q hq' => ?_, ?_, ?_⟩
      · have : (U.applyV τ).bind (fun p => e.applyV τ p.1 p.2) = some q := hq'
        rw [hq] at this; cases this
      · exact (UpdElem.toLS_fresh hA hF0 e he hf₁ hn₁).1
      · exact (UpdElem.toLS_fresh hA hF0 e he hf₁ hn₁).2 ▸ hn₁
    | some p =>
      obtain ⟨he₁, he₂, hf₂, hn₂⟩ := UpdElem.toLS_sound hA hF0 e he (ha₁ p hq) hf₁ hn₁
      refine ⟨?_, fun q hq' => he₂ q (by
        have : (U.applyV τ).bind (fun p => e.applyV τ p.1 p.2) = some q := hq'
        rwa [hq] at this), hf₂, hn₂ ▸ hn₁⟩
      simp only [Option.map_some, Option.bind_some]
      exact he₁
  | decl U x r ih =>
    intro ρ' gd h
    have h' : (U.toLS ρ₀).bind (fun p => (r.toL ρ₀).map fun b =>
      (p.1.push (some b.1), seqL p.2 b.2)) = some (ρ', gd) := h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h'
    obtain ⟨⟨ρ₁, gd₁⟩, hU, ⟨b, gdb⟩, hr, hp⟩ := h'
    cases hp
    obtain ⟨hg₁, ha₁, hf₁, hn₁⟩ := ih hU
    obtain ⟨hgb, hvb, hfb⟩ := Rhs.toL_sound hA hF0 r hr
    refine ⟨?_, fun q hq => ?_, ⟨hf₁.stor.mono (Nat.le_succ _), hf₁.mem.mono (Nat.le_succ _),
      ⟨fun b' hb' => by cases hb'; exact hfb.mono (Nat.le_trans hn₁ (Nat.le_succ _)),
        hf₁.loc.mono (Nat.le_succ _)⟩⟩, Nat.le_trans hn₁ (Nat.le_succ _)⟩
    · show (seqL gd₁ gdb).eval g₀ ν = Option.map _ ((U.applyV τ).bind _)
      rw [seqL_eval, hg₁, hgb]
      cases U.applyV τ <;> try rfl
      simp only [Option.map_some, Option.bind_some]
      cases r.eval τ <;> rfl
    · have hq' : (U.applyV τ).bind (fun p => (r.eval τ).bind fun v => some (p.1, p.2.push v)) =
          some q := hq
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hq'
      obtain ⟨p, hp, v, hv, rfl⟩ := hq'
      have hag := ha₁ p hp
      refine ⟨hag.stor, hag.mem, hag.tx, hag.bal, fun {u} j b' hj => ?_⟩
      cases j with
      | here =>
        simp only [SymS.push, BEnv.get, Option.some.injEq] at hj
        subst hj
        exact hvb v hv
      | there j => exact hag.loc j b' hj
  | pop U h ih =>
    intro ρ' gd hh
    have h' : (U.toLS ρ₀).map
        (fun p => ((⟨p.1.loc.drop h, p.1.stor, p.1.mem, p.1.next⟩ : SymS C _), p.2)) =
        some (ρ', gd) := hh
    rw [Option.map_eq_some_iff] at h'
    obtain ⟨⟨ρ₁, gd₁⟩, hU, hp⟩ := h'
    cases hp
    obtain ⟨hg₁, ha₁, hf₁, hn₁⟩ := ih hU
    refine ⟨?_, fun q hq => ?_, ⟨hf₁.stor, hf₁.mem, BEnv.Fresh.drop h hf₁.loc⟩, hn₁⟩
    · show _ = Option.map _ ((U.applyV τ).bind _)
      rw [hg₁]; cases U.applyV τ <;> rfl
    · have hq' : (U.applyV τ).bind (fun p => some (p.1, p.2.drop h)) = some q := hq
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hq'
      obtain ⟨p, hp, rfl⟩ := hq'
      have hag := ha₁ p hp
      refine ⟨hag.stor, hag.mem, hag.tx, hag.bal, fun {u} j b' hj => ?_⟩
      rw [BEnv.get_drop] at hj
      exact hag.loc _ b' hj
  | drop U h ih =>
    intro ρ' gd hh
    have h' : (U.toLS ρ₀).map
        (fun p => ((⟨p.1.loc.thin h, p.1.stor, p.1.mem, p.1.next⟩ : SymS C _), p.2)) =
        some (ρ', gd) := hh
    rw [Option.map_eq_some_iff] at h'
    obtain ⟨⟨ρ₁, gd₁⟩, hU, hp⟩ := h'
    cases hp
    obtain ⟨hg₁, ha₁, hf₁, hn₁⟩ := ih hU
    refine ⟨?_, fun q hq => ?_, ⟨hf₁.stor, hf₁.mem, BEnv.Fresh.thin h hf₁.loc⟩, hn₁⟩
    · show _ = Option.map _ ((U.applyV τ).bind _)
      rw [hg₁]; cases U.applyV τ <;> rfl
    · have hq' : (U.applyV τ).bind (fun p => some (p.1, p.2.thin h)) = some q := hq
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hq'
      obtain ⟨p, hp, rfl⟩ := hq'
      have hag := ha₁ p hp
      refine ⟨hag.stor, hag.mem, hag.tx, hag.bal, fun {u} j b' hj => ?_⟩
      rw [BEnv.get_thin] at hj
      exact hag.loc _ b' hj

/-- A full array, read: where `fullL` is `true`, the storage and path
return and the array there is full. -/
theorem fullL_true {st : LTm C .st} {E : Ty} {q : LTm C (.path (.ref (.array E)))}
    (h : ((fullL st q).eval g₀ ν : Option Bool) = some true) :
    ∃ w r, (st.eval g₀ ν : Option (Storage C)) = some w ∧ (q.eval g₀ ν : Option (SRef C _)) = some r ∧
      w.full r = true := by
  unfold fullL at h
  rw [LTm.eval_app2, Op2.eval_eq_evalM] at h
  cases hl : ((LTm.app2 .len st q).eval g₀ ν : Option PrimTy.uint.Denote) with
  | none => rw [hl] at h; cases h
  | some l =>
    rw [hl] at h
    have hl1 : l.1 = ((2 ^ 256 - 1 : Nat) : Int) := by
      have h' : BinOp.evalT .eqB l (uintOfNat (2 ^ 256 - 1)) = some true := h
      have h'' : (some (decide (l.1 = (uintOfNat (2 ^ 256 - 1)).1)) : Option Bool) = some true := h'
      simp only [Option.some.injEq, decide_eq_true_eq] at h''
      rw [h'', uintOfNat_val (Nat.sub_one_lt (Nat.ne_of_gt (Nat.two_pow_pos 256)))]
    rw [LTm.eval_app2, Op2.eval_eq_evalM] at hl
    cases hs : (st.eval g₀ ν : Option (Storage C)) with
    | none => rw [hs] at hl; cases hl
    | some w =>
      cases hr : (q.eval g₀ ν : Option (SRef C _)) with
      | none => rw [hs, hr] at hl; cases hl
      | some r =>
        rw [hs, hr] at hl
        refine ⟨w, r, rfl, rfl, ?_⟩
        have hl' : w.len r = some l := hl
        unfold Storage.len at hl'
        unfold Storage.full
        cases hf : w.find r with
        | none => rw [hf] at hl'; cases hl'
        | some v =>
          rw [hf] at hl'
          have hl'' : lenU (SVal.view v : ArrView E).n (SVal.view v : ArrView E).hn = l :=
            Option.some.inj hl'
          subst hl''
          have hn : (SVal.view v : ArrView E).n = 2 ^ 256 - 1 := Int.ofNat.inj hl1
          show (!decide ((SVal.view v : ArrView E).n + 1 < 2 ^ 256)) = true
          simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]
          omega

/-- **What `Tm.exhL` reads**: where it is `true`, the term is a push out of
gas (`Tm.exhB`). -/
theorem Tm.exhL_sound (hA : Agrees g₀ ν ρ₀ τ) {s : Srt} (t : Tm C Γ s) {X : LTm C (.val .bool)}
    (h : t.exhL ρ₀ = some X) (hX : (X.eval g₀ ν : Option Bool) = some true) : t.exhB τ = true := by
  cases t with
  | app2 o x y =>
    cases o <;> simp only [Tm.exhL, Op2.exhL, reduceCtorEq] at h <;>
    · obtain ⟨st', hst, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨q', hq, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨w, r, hw, hr, hfull⟩ := fullL_true hX
      have dx : (st'.eval g₀ ν : Option (Storage C)) = x.eval τ := Tm.toL_drel hA x st' hst
      have dy : (q'.eval g₀ ν : Option (SRef C _)) = y.eval τ := Tm.toL_drel hA y q' hq
      rw [hw] at dx
      rw [hr] at dy
      simp only [Tm.exhB, ← dx, ← dy, Op2.exhB, hfull, Bool.true_or]
  | app3 o x y z =>
    cases o <;> simp only [Tm.exhL, Op3.exhL, reduceCtorEq] at h
    obtain ⟨st', hst, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨q', hq, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨v', hv, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [LTm.eval_kite] at hX
    cases hfl : ((fullL st' q').eval g₀ ν : Option Bool) with
    | none => rw [hfl] at hX; cases hX
    | some b =>
      rw [hfl] at hX
      cases b with
      | false => cases hX
      | true =>
        obtain ⟨w, r, hw, hr, hfull⟩ := fullL_true hfl
        have hv' : (v'.eval g₀ ν).isSome = true := by
          change ((seqL v' LTm.tt).eval g₀ ν : Option Bool) = some true at hX
          rw [seqL_eval] at hX
          cases hve : v'.eval g₀ ν with
          | none => rw [hve] at hX; cases hX
          | some _ => rfl
        have dx : (st'.eval g₀ ν : Option (Storage C)) = x.eval τ := Tm.toL_drel hA x st' hst
        have dy : (q'.eval g₀ ν : Option (SRef C _)) = y.eval τ := Tm.toL_drel hA y q' hq
        have dz := Tm.toL_drel hA z v' hv
        obtain ⟨vv, hvv⟩ := Option.isSome_iff_exists.1 hv'
        have hz : z.eval τ = some vv := by rw [← dz, hvv]
        rw [hw] at dx
        rw [hr] at dy
        simp only [Tm.exhB, ← dx, ← dy, hz, Op3.exhB, hfull, Bool.true_or]
  | _ => simp only [Tm.exhL, reduceCtorEq] at h

/-- **What `Upd.exhL` reads**: where it is `true`, the update is out of gas. -/
theorem Upd.exhL_sound (hA : Agrees g₀ ν ρ₀ τ) {Δ : Ctx} (U : Upd C Γ Δ) {X : LTm C (.val .bool)}
    (h : U.exhL ρ₀ = some X) (hX : (X.eval g₀ ν : Option Bool) = some true) : U.exh τ = true := by
  unfold Upd.exhL at h
  split at h
  · rename_i s
    have hs := Tm.exhL_sound hA s h hX
    simp only [Upd.exh, Upd.exhAny, Upd.exhOk, UpdElem.exhB, hs, Bool.or_true, Bool.false_or,
      Bool.true_and, Bool.and_self]
  · cases h

end Upd

/-! ## Formulas, by position -/

section Fml

variable {g₀ : State C []}

theorem Tm.retsS_eval {Γ : Ctx} (τ : State C Γ) {p : PrimTy} {t : Tm C Γ (.val p)}
    (h : t.retsS = true) : ∃ x, t.eval τ = some x := by
  cases t with
  | pvV i => exact ⟨_, rfl⟩
  | app0 o =>
    cases o <;> simp only [Tm.retsS, reduceCtorEq, Bool.false_eq_true] at h <;> exact ⟨_, rfl⟩
  | _ => simp only [Tm.retsS, Bool.false_eq_true] at h

theorem Fml.eqDView?_some {Γ : Ctx} {φ ψ : Fml C Γ} {p : PrimTy} {a b : Tm C Γ (.val p)}
    (h : Fml.eqDView? φ ψ = some ⟨p, a, b⟩) : Fml.and φ ψ = Fml.eqD a b := by
  unfold Fml.eqDView? at h
  split at h
  · rename_i p₁ a₁ q b₁ r a' b'
    split at h
    · rename_i hpq
      obtain ⟨rfl, rfl⟩ := hpq
      split at h
      · rename_i hb
        simp only [Bool.and_eq_true] at hb
        obtain rfl := Tm.eq_of_beqR hb.1
        obtain rfl := Tm.eq_of_beqR hb.2
        simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h
        cases h
        rfl
      · cases h
    · cases h
  · cases h

theorem Agrees.pushQ {ν : AEnv} {Γ : Ctx} {ρ : SymS C Γ} {τ : State C Γ} (hA : Agrees g₀ ν ρ τ)
    (hF : ρ.Fresh) (p : PrimTy) (v : p.Denote) :
    Agrees g₀ (ν.set p ρ.next v) (ρ.pushQ p) (τ.push (t := .val p) v) := by
  refine ⟨?_, ?_, hA.tx, hA.bal, fun {u} j b hj => ?_⟩
  · show (ρ.stor.eval g₀ (ν.set p ρ.next v) : Option (Storage C)) = some τ.storage
    rw [hF.stor g₀ ν p ρ.next v (Nat.le_refl _)]; exact hA.stor
  · show (ρ.mem.eval g₀ (ν.set p ρ.next v) : Option (Grown _ _)).map Grown.forget = _
    rw [hF.mem g₀ ν p ρ.next v (Nat.le_refl _)]; exact hA.mem
  · rw [State.locV_push]
    cases j with
    | here =>
      simp only [SymS.pushQ, SymS.push, BEnv.get, Option.some.injEq] at hj
      subst hj
      rw [LTm.eval_var, AEnv.get_set_self]
      rfl
    | there j =>
      rw [(hF.loc.get j b hj) g₀ ν p ρ.next v (Nat.le_refl _)]
      exact hA.loc j b hj

theorem SymS.Fresh.pushQ {Γ : Ctx} {ρ : SymS C Γ} (hF : ρ.Fresh) (p : PrimTy) :
    (ρ.pushQ p).Fresh :=
  ⟨hF.stor.mono (Nat.le_succ _), hF.mem.mono (Nat.le_succ _),
    ⟨(fun b hb => by
      simp only [SymS.pushQ, SymS.push, Option.some.injEq] at hb
      subst hb
      intro g ν q k v hk
      simp only [SymS.pushQ, SymS.push] at hk
      rw [LTm.eval_var, LTm.eval_var, AEnv.get_set_ne _ _ _ _ (by omega)]),
    hF.loc.mono (Nat.le_succ _)⟩⟩

theorem Agrees.push {ν : AEnv} {Γ : Ctx} {ρ : SymS C Γ} {τ : State C Γ} (hA : Agrees g₀ ν ρ τ)
    {t : LTy} (v : t.TDenote C τ.H) : Agrees g₀ ν (ρ.push (t := t) none) (τ.push v) := by
  refine ⟨hA.stor, hA.mem, hA.tx, hA.bal, fun {u} j b hj => ?_⟩
  rw [State.locV_push]
  cases j with
  | here => simp only [SymS.push, BEnv.get, reduceCtorEq] at hj
  | there j => exact hA.loc j b hj

theorem SymS.Fresh.push {Γ : Ctx} {ρ : SymS C Γ} (hF : ρ.Fresh) (t : LTy) :
    (ρ.push (t := t) none).Fresh :=
  ⟨hF.stor.mono (Nat.le_succ _), hF.mem.mono (Nat.le_succ _),
    ⟨(fun b hb => by cases hb), hF.loc.mono (Nat.le_succ _)⟩⟩

theorem guardM_holds {ν : AEnv} {Γ : Ctx} {τ : State C Γ} {Δ : Ctx} (m : Modality) (U : Upd C Γ Δ)
    {x : Option (LTm C (.val .bool))} {gd : LTm C (.val .bool)} {ψ : LFml C} {φ : Fml C Δ}
    (hx : ∀ X, x = some X → (X.eval g₀ ν : Option Bool) = some true → U.exh τ = true)
    (hg : (gd.eval g₀ ν : Option Bool) = (U.applyV τ).map (fun _ => true))
    (hrest : ∀ q, U.applyV τ = some q → ψ.holds g₀ ν → ∀ σ' : State C Δ, σ'.glob = q.1.1 →
      (∀ {t : LTy} (i : Idx Δ t), σ'.getV i = q.2 t i) → holds σ' φ)
    (h : (guardM m x gd ψ).holds g₀ ν) : holds τ (.upd m U φ) := by
  show U.afterT m τ (holds · φ)
  rw [Upd.afterT_applyV]
  have hgd : (LFml.eq gd gd).holds g₀ ν ↔ (U.applyV τ).isSome = true := by
    rw [LFml.holds_rets, hg]
    cases U.applyV τ with
    | none => exact ⟨fun ⟨_, h⟩ => (nomatch h), fun h => (nomatch h)⟩
    | some _ => exact ⟨fun _ => rfl, fun _ => ⟨true, rfl⟩⟩
  cases hq : U.applyV τ with
  | none =>
    cases m with
    | box => exact .inl trivial
    | diamond =>
      cases x with
      | none =>
        have h' := (hgd.1 h.1)
        rw [hq] at h'
        cases h'
      | some X =>
        refine .inr (hx X rfl ?_)
        have h1 : ¬ (LFml.not (LFml.eq X .tt)).holds g₀ ν := fun hn => by
          have h' := hgd.1 (h.1 hn)
          rw [hq] at h'
          cases h'
        have h2 : (LFml.eq X .tt).holds g₀ ν := Classical.byContradiction h1
        obtain ⟨b, hb, hb'⟩ := (LFml.holds_eq_iff _ _ _ _).1 h2
        cases hb'
        exact hb
  | some q =>
    have hgq : (LFml.eq gd gd).holds g₀ ν := hgd.2 (by rw [hq]; rfl)
    cases m with
    | box => exact hrest q hq (h hgq)
    | diamond =>
      cases x with
      | none => exact hrest q hq h.2
      | some X => exact hrest q hq (h.2 hgq)

/-- A hidden binder read as a quantifier (`LFml.allB`): what holds for
every atom at its position holds for every value it binds. -/
theorem Fml.allB_push {Γ : Ctx} {t : LTy} {ρ : SymS C Γ} {τ : State C Γ} {ν : AEnv}
    (hA : Agrees g₀ ν ρ τ) (hF : ρ.Fresh) {ψ₁ : LFml C} {P : State C (t :: Γ) → Prop}
    (ih : ∀ (τ' : State C (t :: Γ)) (ν' : AEnv), Agrees g₀ ν' (ρ.pushB t) τ' →
      (ρ.pushB t).Fresh → ψ₁.holds g₀ ν' → P τ')
    (hψ : (LFml.allB t ρ.next ψ₁).holds g₀ ν) (v : t.TDenote C τ.H) : P (τ.push v) := by
  cases t with
  | val p => exact ih _ _ (hA.pushQ hF p v) (hF.pushQ p) (hψ v)
  | _ => exact ih _ _ (hA.push v) (hF.push _) hψ

/-- **A formula pushed in** implies the formula at the positive polarity,
and follows from it at the negative one. -/
theorem Fml.toLS_sound : ∀ {Γ : Ctx} (φ : Fml C Γ) (pos : Bool) {ρ : SymS C Γ} {ψ : LFml C},
    φ.toLS pos ρ = some ψ → ∀ (τ : State C Γ) (ν : AEnv), Agrees g₀ ν ρ τ → ρ.Fresh →
    (pos = true → ψ.holds g₀ ν → holds τ φ) ∧ (pos = false → holds τ φ → ψ.holds g₀ ν)
  | _, .tt, _, _, _, h, _, _, _, _ => by
    cases h; exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  | _, .eq (p := p) a b, pos, ρ, ψ, h, τ, ν, hA, _ => by
    have h' : (if pos || (a.retsS && b.retsS) then
        (a.toL ρ).bind fun a' => (b.toL ρ).map fun b' => LFml.eq a' b' else none) = some ψ := h
    split at h'
    · rename_i hc
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h'
      obtain ⟨a', ha', b', hb', rfl⟩ := h'
      have hda : (a'.eval g₀ ν : Option p.Denote) = a.eval τ := Tm.toL_drel hA a a' ha'
      have hdb : (b'.eval g₀ ν : Option p.Denote) = b.eval τ := Tm.toL_drel hA b b' hb'
      refine ⟨fun _ hψ => ?_, fun hpos hφ => ?_⟩
      · rw [LFml.holds_eq_iff] at hψ
        obtain ⟨x, hx, hy⟩ := hψ
        rw [hda] at hx; rw [hdb] at hy
        show a.denote τ = b.denote τ
        rw [Tm.denote_eval τ a x hx, Tm.denote_eval τ b x hy]
      · subst hpos
        simp only [Bool.false_or, Bool.and_eq_true] at hc
        obtain ⟨x, hx⟩ := Tm.retsS_eval τ hc.1
        obtain ⟨y, hy⟩ := Tm.retsS_eval τ hc.2
        have hφ' : a.denote τ = b.denote τ := hφ
        rw [Tm.denote_eval τ a x hx, Tm.denote_eval τ b y hy] at hφ'
        obtain rfl : x = y := Option.some.inj hφ'
        rw [LFml.holds_eq_iff]
        exact ⟨x, by rw [hda, hx], by rw [hdb, hy]⟩
    · cases h'
  | _, .defined (p := p) t, pos, ρ, ψ, h, τ, ν, hA, _ => by
    have h' : (t.toL ρ).map (fun t' => LFml.eq t' t') = some ψ := h
    rw [Option.map_eq_some_iff] at h'
    obtain ⟨t', ht', rfl⟩ := h'
    have hd : (t'.eval g₀ ν : Option p.Denote) = t.eval τ := Tm.toL_drel hA t t' ht'
    have key : (LFml.eq t' t').holds g₀ ν ↔ holds τ (.defined t) := by
      rw [LFml.holds_rets, holds_defined, hd]
      constructor
      · rintro ⟨x, hx⟩; rw [hx]; exact nofun
      · intro h; exact Option.ne_none_iff_exists'.1 h
    exact ⟨fun _ => key.1, fun _ => key.2⟩
  | _, .not φ, pos, ρ, ψ, h, τ, ν, hA, hF => by
    have h' : (φ.toLS (!pos) ρ).map LFml.not = some ψ := h
    rw [Option.map_eq_some_iff] at h'
    obtain ⟨ψ₁, h₁, rfl⟩ := h'
    obtain ⟨ih₁, ih₂⟩ := Fml.toLS_sound φ (!pos) h₁ τ ν hA hF
    refine ⟨fun hp hψ hφ => hψ (ih₂ (by simp only [hp, Bool.not_true]) hφ),
      fun hp hφ hψ => hφ (ih₁ (by simp only [hp, Bool.not_false]) hψ)⟩
  | _, .and φ₁ φ₂, pos, ρ, ψ, h, τ, ν, hA, hF => by
    have h' : (match Fml.eqDView? φ₁ φ₂ with
      | some ⟨_, a, b⟩ => (a.toL ρ).bind fun a' => (b.toL ρ).map fun b' => LFml.eq a' b'
      | none => (φ₁.toLS pos ρ).bind fun ψ₁ => (φ₂.toLS pos ρ).map fun ψ₂ => .and ψ₁ ψ₂) =
        some ψ := h
    split at h'
    · rename_i p a b he
      rw [Fml.eqDView?_some he]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h'
      obtain ⟨a', ha', b', hb', rfl⟩ := h'
      have hda : (a'.eval g₀ ν : Option p.Denote) = a.eval τ := Tm.toL_drel hA a a' ha'
      have hdb : (b'.eval g₀ ν : Option p.Denote) = b.eval τ := Tm.toL_drel hA b b' hb'
      have key : (LFml.eq a' b').holds g₀ ν ↔ holds τ (Fml.eqD a b) := by
        rw [LFml.holds_eq_iff, holds_eqD, hda, hdb]
      exact ⟨fun _ => key.1, fun _ => key.2⟩
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h'
      obtain ⟨ψ₁, h₁, ψ₂, h₂, rfl⟩ := h'
      obtain ⟨i₁, j₁⟩ := Fml.toLS_sound φ₁ pos h₁ τ ν hA hF
      obtain ⟨i₂, j₂⟩ := Fml.toLS_sound φ₂ pos h₂ τ ν hA hF
      exact ⟨fun hp hψ => ⟨i₁ hp hψ.1, i₂ hp hψ.2⟩, fun hp hφ => ⟨j₁ hp hφ.1, j₂ hp hφ.2⟩⟩
  | _, .imp φ₁ φ₂, pos, ρ, ψ, h, τ, ν, hA, hF => by
    have h' : (φ₁.toLS (!pos) ρ).bind (fun ψ₁ => (φ₂.toLS pos ρ).map fun ψ₂ => LFml.imp ψ₁ ψ₂) =
      some ψ := h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h'
    obtain ⟨ψ₁, h₁, ψ₂, h₂, rfl⟩ := h'
    obtain ⟨i₁, j₁⟩ := Fml.toLS_sound φ₁ (!pos) h₁ τ ν hA hF
    obtain ⟨i₂, j₂⟩ := Fml.toLS_sound φ₂ pos h₂ τ ν hA hF
    refine ⟨fun hp hψ hφ₁ => i₂ hp (hψ (j₁ (by simp only [hp, Bool.not_true]) hφ₁)),
      fun hp hφ hψ₁ => j₂ hp (hφ (i₁ (by simp only [hp, Bool.not_false]) hψ₁))⟩
  | _, .upd m U φ, pos, ρ, ψ, h, τ, ν, hA, hF => by
    have h' : (if pos then (U.toLS ρ).bind fun p => (φ.toLS pos p.1).map fun φ' =>
      guardM m (U.exhL ρ) p.2 φ' else none) = some ψ := h
    split at h'
    · rename_i hp
      subst hp
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h'
      obtain ⟨⟨ρ', gd⟩, hU, ψ', hφ, rfl⟩ := h'
      obtain ⟨hg, hag, hf', -⟩ := Upd.toLS_sound hA hF U hU
      refine ⟨fun _ hψ => guardM_holds m U (fun X hX hXt => Upd.exhL_sound hA U hX hXt) hg
        (fun q hq hψ' σ' hσ hl => ?_) hψ, fun h => by cases h⟩
      have hA' : Agrees g₀ ν ρ' σ' := by
        have hl' : σ'.locV = q.2 := funext fun _ => funext fun i => hl i
        show AgreesV g₀ ν ρ' σ'.glob σ'.locV
        rw [hσ, hl']
        exact hag q hq
      exact (Fml.toLS_sound φ true hφ σ' ν hA' hf').1 rfl hψ'
    · cases h'
  | _, .modal .., pos, ρ, ψ, h, τ, ν, hA, hF => by
    have h' : (if pos then some LFml.ff else none) = some ψ := h
    split at h'
    · cases h'; exact ⟨fun _ hψ => (hψ trivial).elim, fun hp => by subst hp; contradiction⟩
    · cases h'
  | _, .havoc _, _, _, _, h, _, _, _, _ => by cases h
  | _, .anon .., _, _, _, h, _, _, _, _ => by cases h
  | _, .all x p φ, pos, ρ, ψ, h, τ, ν, hA, hF => by
    have h' : (φ.toLS pos (ρ.pushQ p)).map (fun φ' => LFml.all ρ.next p φ') = some ψ := h
    rw [Option.map_eq_some_iff] at h'
    obtain ⟨ψ₁, h₁, rfl⟩ := h'
    refine ⟨fun hp hψ v => ?_, fun hp hφ v => ?_⟩
    · exact (Fml.toLS_sound φ pos h₁ (τ.push (t := .val p) v) (ν.set p ρ.next v)
        (hA.pushQ hF p v) (hF.pushQ p)).1 hp (hψ v)
    · exact (Fml.toLS_sound φ pos h₁ (τ.push (t := .val p) v) (ν.set p ρ.next v)
        (hA.pushQ hF p v) (hF.pushQ p)).2 hp (hφ v)
  | _, .bind m x t φ, pos, ρ, ψ, h, τ, ν, hA, hF => by
    have h' : (if pos then (φ.toLS pos (ρ.pushB t)).map (LFml.allB t ρ.next) else none) =
      some ψ := h
    split at h'
    · rename_i hp
      subst hp
      rw [Option.map_eq_some_iff] at h'
      obtain ⟨ψ₁, h₁, rfl⟩ := h'
      refine ⟨fun _ hψ => fun v => ?_, fun h => by cases h⟩
      exact Fml.allB_push hA hF (fun τ' ν' hA' hF' => (Fml.toLS_sound φ true h₁ τ' ν' hA' hF').1 rfl)
        hψ v
    · cases h'

/-- The empty state agrees with every typed state of the empty context. -/
theorem Agrees.init (τ : State C []) (ν : AEnv) : Agrees τ ν SymS.init τ :=
  ⟨rfl, rfl, rfl, rfl, fun i => nomatch i⟩

theorem SymS.Fresh.init : (SymS.init : SymS C []).Fresh :=
  ⟨Fresh.app0 _ _, Fresh.app0 _ _, trivial⟩

end Fml

/-- **A leaf whose reduction, before the elimination, is valid, is
valid** (`Fml.toLS_sound`). -/
theorem _root_.Solidity.Valid.of_toLS {φ : Fml C []} {ψ : LFml C}
    (h : φ.toLS true SymS.init = some ψ) (hψ : ψ.Valid) : Valid φ := fun τ =>
  (Fml.toLS_sound φ true h τ AEnv.dflt (Agrees.init τ AEnv.dflt) SymS.Fresh.init).1 rfl
    (hψ τ AEnv.dflt)

/-- **`sol_decide`'s reduction is sound**: a scoped leaf whose reduction is
valid is valid. -/
theorem _root_.Solidity.Valid.of_reduceS {φ : Fml C []} {ψ : LFml C} (h : φ.reduceS = some ψ)
    (hψ : ψ.Valid) : Valid φ := by
  intro τ
  unfold Fml.reduceS at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨ψ₀, h₀, rfl⟩ := h
  have hh : ψ₀.holds τ AEnv.dflt := (LFml.elim_holds τ ψ₀ AEnv.dflt).1 (hψ τ AEnv.dflt)
  exact (Fml.toLS_sound φ true h₀ τ AEnv.dflt (Agrees.init τ AEnv.dflt) SymS.Fresh.init).1 rfl hh

end Decide

end Solidity
