import Solidity.Calculus.Step
import Solidity.Update
import Solidity.Theory.Observe
import Solidity.Typing.Soundness
import Solidity.Semantics.RunFrame
import Solidity.Theory.Bridge.Denote

/-!
# Terms and updates read in a state; where an update lands

What `holds` (`Calculus/Logic.lean`) reads a term and an update by.

* The readers (`Tm.evalT`, `Tm.denoteT`, `Rhs.evalT`): a term on the typed
  state, its global part erased (`State.globE`), a local read by its
  position and erased at its type (`State.getE`).
* What an update leaves in each local (`Upd.held`: a local it kept, or the
  right-hand side it last wrote), and where it lands (decision U2, chosen at
  W9.7): `Upd.Lands σ₀ U g σ'`, `U`'s global part `g` (`Upd.globT`) is
  `σ'`'s and each local of `σ'` holds what `Upd.held` says, read in `σ₀`;
  `Upd.afterT` is `holds`' update clause.
* What an update leaves, computed on the typed state: `Upd.applyV`, its
  global part and the locals' values (`Locs`), what a landed state reads
  (`Upd.lands_iff_applyV`, `Upd.afterT_applyV`); the closer, the decision
  procedure and the rules' soundness read updates by it.
-/

namespace Solidity
open Semantics (Value SVal MVal Seg Halt Res lookupBy setBy allocDefault applyUnOp)
open Solidity (evalBinop unopCheck)
open Theory Theory.StValue
open Solidity (Srt Op0 Op1 Op2 Op3 Modality IntOp)

variable {C : Contract}

/-- `p` after an outcome under `m`: `p` of the state, or `m.onHalt`. -/
def _root_.Solidity.Modality.afterC {α : Type} (m : Modality) (p : α → Prop) : Res α → Prop
  | .ok τ => p τ
  | .error _ => m.onHalt

/-! ## What an update leaves in a local -/

/-- What a local of type `t` holds after an update applied in `Γ`: a local
of `Γ` it kept, or the right-hand side last written to it. -/
inductive Held (C : Contract) (Γ : Ctx) (t : LTy) : Type where
  | pos (i : Idx Γ t)
  | rhs (r : Rhs C Γ t)

/-- What every local of `Δ` holds after an update from `Γ` to `Δ`. -/
def Subst (C : Contract) (Γ Δ : Ctx) : Type := {t : LTy} → Idx Δ t → Held C Γ t

theorem Idx.ty_eq_of_toNat {Γ : Ctx} {t u : LTy} {i : Idx Γ t} {j : Idx Γ u}
    (h : i.toNat = j.toNat) : t = u := by
  have hi := i.getElem?_toNat
  have hj := j.getElem?_toNat
  rw [h, hj] at hi
  exact (Option.some.inj hi).symm

/-- The local `i` holds `r`. -/
def Subst.set {Γ Δ : Ctx} (s : Subst C Γ Δ) {t : LTy} (i : Idx Δ t) (r : Rhs C Γ t) :
    Subst C Γ Δ :=
  fun j => if h : i.toNat = j.toNat then .rhs (Idx.ty_eq_of_toNat h ▸ r) else s j

/-- A local pushed, holding `h`. -/
def Subst.cons {Γ Δ : Ctx} {t : LTy} (s : Subst C Γ Δ) (h : Held C Γ t) : Subst C Γ (t :: Δ)
  | _, .here => h
  | _, .there j => s j

/-- What an update leaves in each local. -/
def Upd.held {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Subst C Γ Δ
  | _, .nil => fun i => .pos i
  | _, .snoc U (.local i r) => Subst.set (Upd.held U) i r
  | _, .snoc U _ => Upd.held U
  | _, .decl U _ r => Subst.cons (Upd.held U) (.rhs r)
  | _, .pop U h => fun j => Upd.held U (j.ext h)
  | _, .drop U h => fun j => Upd.held U (j.wk h)

/-! ## The readers

A term read on the typed state: the global part erased (`State.globE`), a
local by `TEnv.get`, erased at its type (`State.getE`). -/

section Typed

variable {Γ : Ctx}

/-- The path an alias is bound to; an unset one reverts. -/
def State.aliasPathT (σ : State C Γ) {R : RefTy} (i : Idx Γ (.alias R)) :
    Res (Name × List Seg) :=
  match (TEnv.get i σ.env : Option (SRef C (.ref R))) with
  | some r => pure r.erase
  | none => .error .revert

/-- The object a memory local names; an unset one reverts, as an unset
alias does (decision 17'). -/
def State.memRefT (σ : State C Γ) {R : RefTy} (i : Idx Γ (.mem R)) : Res Nat :=
  match (TEnv.get i σ.env : Option (HRef σ.H R)) with
  | some r => pure r.id
  | none => .error .revert

/-- A term read in the typed state `σ`: a local by its position, a symbol on
the global part. -/
def Tm.evalT (σ : State C Γ) : {s : Srt} → Tm C Γ s → s.Ev
  | _, .pvV i => pure (σ.getE i)
  | _, .pvP i => σ.aliasPathT i
  | _, .pvS i => pure { σ.globE with storage := σ.getE i }
  | _, .pvI i => σ.memRefT i
  | _, .netOf i a => do
    let l : List (Int × Int) := σ.getE i
    pure (.int ((lookupBy (← (← a.evalT σ).asInt) l).getD 0))
  | _, .app0 o => o.eval σ.globE
  | _, .app1 o _ a => o.eval σ.globE (a.evalT σ)
  | _, .app2 o a b => o.eval σ.globE (a.evalT σ) (b.evalT σ)
  | _, .app3 o a b c => o.eval σ.globE (a.evalT σ) (b.evalT σ) (c.evalT σ)

/-- A term in the Theory, read in the typed state `σ` (over
`State.abs σ.globE`, `Update.lean`'s `OpN.denote`). -/
def Tm.denoteT (σ : State C Γ) : {s : Srt} → Tm C Γ s → s.Den
  | _, .pvV i => .prim (σ.getE i)
  | _, .pvP i => match σ.aliasPathT i with
    | .ok (r, segs) => rootPath r segs
    | .error _ => []
  | _, .pvS i => SVal.abs.fields (σ.getE i)
  | _, .pvI _ => ()
  | _, .netOf i a => match a.denoteT σ with
    | .prim (.int n) => .prim (.int ((lookupBy n (σ.getE i : List (Int × Int))).getD 0))
    | _ => .st .mtSt
  | _, .app0 o => o.denote σ.globE
  | _, .app1 o _ a => o.denote σ.globE (a.denoteT σ)
  | _, .app2 o a b => o.denote σ.globE (a.evalT σ) (b.evalT σ) (a.denoteT σ) (b.denoteT σ)
  | _, .app3 o a b c => o.denote (a.denoteT σ) (b.denoteT σ) (c.denoteT σ)

/-- What a local is set to, read in the typed state `σ₀`. -/
def Rhs.evalT (σ₀ : State C Γ) : {t : LTy} → Rhs C Γ t → Res (t.Denote C)
  | _, .val t => t.evalT σ₀
  | _, .path p => do pure (some (← p.evalT σ₀))
  | _, .unset => pure none
  | _, .mref i => do pure (some (← i.evalT σ₀))
  | _, .store s => do pure (← s.evalT σ₀).storage
  | _, .saveNet => pure σ₀.net
  | _, .saveNetMt => pure []

end Typed

/-! ## Landing

An update applied in a typed state `σ₀` computes its global part
(`Upd.globT`) and what it leaves in each local (`Upd.held`), read in `σ₀`.
It lands on every typed state with that global part and those locals
(`Upd.Lands`). -/

section Lands

variable {Γ : Ctx}

/-- The global part one element leaves, its right-hand sides read in `σ₀`
(a local's right-hand side is read for its halt). -/
def UpdElem.globT {Δ : Ctx} (σ₀ : State C Γ) :
    UpdElem C Γ Δ → Semantics.State → Res Semantics.State
  | .local _ r, g => do let _ ← r.evalT σ₀; pure g
  | .storage s, g => do
    let st := (← s.evalT σ₀).storage
    pure { g with storage := st }
  | .memory m, g => do
    let μ ← m.evalT σ₀
    pure { g with heap := μ.heap, nextId := μ.nextId }
  | .selfBalance op a, g => do
    let amt ← (← a.evalT σ₀).asInt
    pure { g with selfBalance := op.apply σ₀.globE.selfBalance amt }
  | .net r op a, g => do
    let addr ← (← r.evalT σ₀).asInt
    let amt ← (← a.evalT σ₀).asInt
    pure { g with net := setBy addr (op.apply (g.getNet addr) amt) g.net }
  | .pay r a, g => do
    let addr ← (← r.evalT σ₀).asInt
    let amt ← (← a.evalT σ₀).asInt
    if amt < 0 then .error .revert
    else pure { g with
      net := if addr = σ₀.globE.tx.selfAddress then g.net
        else setBy addr (g.getNet addr - amt) g.net }
  | .netMt r a, g => do
    let addr ← (← r.evalT σ₀).asInt
    let amt ← (← a.evalT σ₀).asInt
    pure { g with net := [(addr, amt)] }
  | .setBalance a, g => do
    let amt ← (← a.evalT σ₀).asInt
    pure { g with selfBalance := amt }

/-- The global part an update applied in `σ₀` leaves. -/
def Upd.globT (σ₀ : State C Γ) : {Δ : Ctx} → Upd C Γ Δ → Res Semantics.State
  | _, .nil => pure σ₀.globE
  | _, .snoc U e => do e.globT σ₀ (← U.globT σ₀)
  | _, .decl U _ r => do
    let g ← U.globT σ₀
    let _ ← r.evalT σ₀
    pure g
  | _, .pop U _ => U.globT σ₀
  | _, .drop U _ => U.globT σ₀

/-- What `U` left in the local `i` of `σ'`, read in `σ₀`. -/
def Held.OKT {Δ : Ctx} (σ₀ : State C Γ) (σ' : State C Δ) {t : LTy} (i : Idx Δ t) :
    Held C Γ t → Prop
  | .pos j => σ'.getE i = σ₀.getE j
  | .rhs r => r.evalT σ₀ = .ok (σ'.getE i)

/-- **`U` applied in `σ₀` lands on `σ'`**: it leaves the global part `g`,
which is `σ'`'s, and in each local of `σ'` what `Upd.held` says. -/
def Upd.Lands {Δ : Ctx} (σ₀ : State C Γ) (U : Upd C Γ Δ) (g : Semantics.State)
    (σ' : State C Δ) : Prop :=
  U.globT σ₀ = .ok g ∧ σ'.globE = g ∧ ∀ {t : LTy} (i : Idx Δ t), Held.OKT σ₀ σ' i (U.held i)

/-- `p` after `U` applied in `σ₀` under `m`: of every typed state it lands
on whose heap typing extends `σ₀`'s, or `m.onHalt` when it halts. -/
def Upd.afterT {Δ : Ctx} (m : Modality) (σ₀ : State C Γ) (U : Upd C Γ Δ)
    (p : State C Δ → Prop) : Prop :=
  match U.globT σ₀ with
  | .error _ => m.onHalt
  | .ok g => ∀ σ' : State C Δ, U.Lands σ₀ g σ' → σ₀.H <+: σ'.H → p σ'

theorem Upd.afterT_imp {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    {p q : State C Δ → Prop} (h : U.afterT m σ₀ p) (hpq : ∀ σ', p σ' → q σ') :
    U.afterT m σ₀ q := by
  unfold Upd.afterT at h ⊢
  split
  · rename_i e he; rw [he] at h; exact h
  · rename_i g hg; rw [hg] at h; exact fun σ' hl hp => hpq σ' (h σ' hl hp)

theorem Upd.afterT_and {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    {p q r : State C Δ → Prop} (hp : U.afterT m σ₀ p) (hq : U.afterT m σ₀ q)
    (h : ∀ σ', p σ' → q σ' → r σ') : U.afterT m σ₀ r := by
  unfold Upd.afterT at hp hq ⊢
  split
  · rename_i e he; rw [he] at hp; exact hp
  · rename_i g hg
    rw [hg] at hp hq
    exact fun σ' hl hx => h σ' (hp σ' hl hx) (hq σ' hl hx)

end Lands

/-! ## The typed kit

What the update laws read `afterT` by: two
states a term reads alike (`State.ReadsAs`), what a local holds after an
update as a value (`Held.OKV`), landing introduced and eliminated
(`Upd.afterT_intro`, `Upd.afterT.of_lands`), and two updates in turn read
as one (`Upd.afterT_seq`). -/

section Kit

variable {Γ : Ctx}

theorem State.aliasPathT_getE (σ : State C Γ) {R : RefTy} (i : Idx Γ (.alias R)) :
    σ.aliasPathT i =
      (match (σ.getE i : Option (Name × List Seg)) with
        | some p => pure p
        | none => .error .revert) := by
  unfold State.aliasPathT State.getE
  generalize (TEnv.get i σ.env : Option (SRef C (.ref R))) = x
  cases x <;> rfl

theorem State.memRefT_getE (σ : State C Γ) {R : RefTy} (i : Idx Γ (.mem R)) :
    σ.memRefT i =
      (match (σ.getE i : Option Nat) with
        | some id => pure id
        | none => .error .revert) := by
  unfold State.memRefT State.getE
  generalize (TEnv.get i σ.env : Option (HRef σ.H R)) = x
  cases x <;> rfl

/-- Two typed states a term reads alike: one global part erased, one local
erased at each position. -/
def State.ReadsAs (σ σ' : State C Γ) : Prop :=
  σ.globE = σ'.globE ∧ ∀ {t : LTy} (i : Idx Γ t), σ.getE i = σ'.getE i

theorem State.ReadsAs.refl (σ : State C Γ) : σ.ReadsAs σ := ⟨rfl, fun _ => rfl⟩

theorem State.ReadsAs.symm {σ σ' : State C Γ} (h : σ.ReadsAs σ') : σ'.ReadsAs σ :=
  ⟨h.1.symm, fun i => (h.2 i).symm⟩

theorem Tm.evalT_congr {σ σ' : State C Γ} (h : σ.ReadsAs σ') :
    {s : Srt} → (t : Tm C Γ s) → t.evalT σ = t.evalT σ'
  | _, .pvV i => by simp only [Tm.evalT, h.2 i]
  | _, .pvP i => by simp only [Tm.evalT, State.aliasPathT_getE, h.2 i]
  | _, .pvS i => by simp only [Tm.evalT, h.1, h.2 i]
  | _, .pvI i => by simp only [Tm.evalT, State.memRefT_getE, h.2 i]
  | _, .netOf i a => by simp only [Tm.evalT, h.2 i, Tm.evalT_congr h a]
  | _, .app0 _ => by simp only [Tm.evalT, h.1]
  | _, .app1 _ _ a => by simp only [Tm.evalT, h.1, Tm.evalT_congr h a]
  | _, .app2 _ a b => by simp only [Tm.evalT, h.1, Tm.evalT_congr h a, Tm.evalT_congr h b]
  | _, .app3 _ a b c => by
    simp only [Tm.evalT, h.1, Tm.evalT_congr h a, Tm.evalT_congr h b, Tm.evalT_congr h c]

theorem Tm.denoteT_congr {σ σ' : State C Γ} (h : σ.ReadsAs σ') :
    {s : Srt} → (t : Tm C Γ s) → t.denoteT σ = t.denoteT σ'
  | _, .pvV i => by simp only [Tm.denoteT, h.2 i]
  | _, .pvP i => by simp only [Tm.denoteT, State.aliasPathT_getE, h.2 i]
  | _, .pvS i => by simp only [Tm.denoteT, h.2 i]
  | _, .pvI _ => rfl
  | _, .netOf i a => by simp only [Tm.denoteT, h.2 i, Tm.denoteT_congr h a]
  | _, .app0 _ => by simp only [Tm.denoteT, h.1]
  | _, .app1 _ _ a => by simp only [Tm.denoteT, h.1, Tm.denoteT_congr h a]
  | _, .app2 _ a b => by
    simp only [Tm.denoteT, h.1, Tm.denoteT_congr h a, Tm.denoteT_congr h b, Tm.evalT_congr h a,
      Tm.evalT_congr h b]
  | _, .app3 _ a b c => by
    simp only [Tm.denoteT, Tm.denoteT_congr h a, Tm.denoteT_congr h b, Tm.denoteT_congr h c]

theorem Rhs.evalT_congr {σ σ' : State C Γ} (h : σ.ReadsAs σ') :
    {t : LTy} → (r : Rhs C Γ t) → r.evalT σ = r.evalT σ'
  | _, .val t => Tm.evalT_congr h t
  | _, .path p => by simp only [Rhs.evalT, Tm.evalT_congr h p]
  | _, .unset => rfl
  | _, .mref i => by simp only [Rhs.evalT, Tm.evalT_congr h i]
  | _, .store s => by simp only [Rhs.evalT, Tm.evalT_congr h s]
  | _, .saveNet => by
    have hn : σ.net = σ'.net := congrArg Semantics.State.net h.1
    simp only [Rhs.evalT, hn]
  | _, .saveNetMt => rfl

theorem UpdElem.globT_congr {Δ : Ctx} {σ σ' : State C Γ} (h : σ.ReadsAs σ') (e : UpdElem C Γ Δ)
    (g : Semantics.State) : e.globT σ g = e.globT σ' g := by
  cases e <;> simp only [UpdElem.globT, Rhs.evalT_congr h, Tm.evalT_congr h, h.1]

theorem Upd.globT_congr {σ σ' : State C Γ} (h : σ.ReadsAs σ') :
    {Δ : Ctx} → (U : Upd C Γ Δ) → U.globT σ = U.globT σ'
  | _, .nil => by simp only [Upd.globT, h.1]
  | _, .snoc U e => by simp only [Upd.globT, Upd.globT_congr h U, UpdElem.globT_congr h e]
  | _, .decl U _ r => by simp only [Upd.globT, Upd.globT_congr h U, Rhs.evalT_congr h r]
  | _, .pop U _ => Upd.globT_congr h U
  | _, .drop U _ => Upd.globT_congr h U

/-- What a local holds after an update, as a value: a local of the state
before, or a right-hand side read in it. -/
def Held.OKV {t : LTy} (σ₀ : State C Γ) (v : t.Denote C) : Held C Γ t → Prop
  | .pos j => v = σ₀.getE j
  | .rhs r => r.evalT σ₀ = .ok v

theorem Held.OKT_iff_OKV {Δ : Ctx} (σ₀ : State C Γ) (σ' : State C Δ) {t : LTy} (i : Idx Δ t)
    (x : Held C Γ t) : Held.OKT σ₀ σ' i x ↔ Held.OKV σ₀ (σ'.getE i) x := by
  cases x <;> exact Iff.rfl

theorem Held.OKV_congr {σ σ' : State C Γ} (h : σ.ReadsAs σ') {t : LTy} (v : t.Denote C) :
    (x : Held C Γ t) → (Held.OKV σ v x ↔ Held.OKV σ' v x)
  | .pos j => by simp only [Held.OKV, h.2 j]
  | .rhs r => by simp only [Held.OKV, Rhs.evalT_congr h r]

theorem Upd.lands_congr {Δ : Ctx} {σ σ' : State C Γ} (h : σ.ReadsAs σ') (U : Upd C Γ Δ)
    (g : Semantics.State) (τ : State C Δ) : U.Lands σ g τ ↔ U.Lands σ' g τ := by
  unfold Upd.Lands
  simp only [Upd.globT_congr h U, Held.OKT_iff_OKV, Held.OKV_congr h]

/-- **States a term reads alike, of one heap typing, give one `afterT`.** -/
theorem Upd.afterT_congr {Δ : Ctx} (m : Modality) {σ σ' : State C Γ} (h : σ.ReadsAs σ')
    (hH : σ.H = σ'.H) (U : Upd C Γ Δ) (p : State C Δ → Prop) :
    U.afterT m σ p ↔ U.afterT m σ' p := by
  unfold Upd.afterT
  rw [Upd.globT_congr h U]
  split
  · exact Iff.rfl
  · rename_i g _
    simp only [Upd.lands_congr h U g, hH]

/-- `afterT` from what it asks: `m.onHalt` where the update halts, `p` of
every typed state it lands on. -/
theorem Upd.afterT_intro {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    {p : State C Δ → Prop} (hh : ∀ e, U.globT σ₀ = .error e → m.onHalt)
    (hp : ∀ g σ', U.Lands σ₀ g σ' → σ₀.H <+: σ'.H → p σ') : U.afterT m σ₀ p := by
  unfold Upd.afterT
  split
  · rename_i e he; exact hh e he
  · exact fun σ' hl hH => hp _ σ' hl hH

/-- What holds after an update holds of a typed state it lands on. -/
theorem Upd.afterT.of_lands {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    {p : State C Δ → Prop} (h : U.afterT m σ₀ p) {g : Semantics.State} {σ' : State C Δ}
    (hl : U.Lands σ₀ g σ') (hH : σ₀.H <+: σ'.H) : p σ' := by
  unfold Upd.afterT at h
  rw [hl.1] at h
  exact h σ' hl hH

/-- Where an update halts, `afterT` is `m.onHalt`. -/
theorem Upd.afterT.of_error {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    {p : State C Δ → Prop} (h : U.afterT m σ₀ p) {e : Halt} (he : U.globT σ₀ = .error e) :
    m.onHalt := by
  unfold Upd.afterT at h
  rw [he] at h
  exact h

/-- **Two updates in turn, read as one**: `W` gives `U` then `V` where
`W` halts where `U` does, and past a state `U` lands on, `W` computes the
global part `V` does there and leaves in each local what `V` leaves. -/
theorem Upd.afterT_seq {Δ₁ Δ₂ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ₁}
    {V : Upd C Δ₁ Δ₂} {W : Upd C Γ Δ₂} {p : State C Δ₂ → Prop}
    (herr : ∀ e, U.globT σ₀ = .error e → ∃ e', W.globT σ₀ = .error e')
    (hglob : ∀ g₁ σ₁, U.Lands σ₀ g₁ σ₁ → W.globT σ₀ = V.globT σ₁)
    (hheld : ∀ g₁ σ₁, U.Lands σ₀ g₁ σ₁ → ∀ {t : LTy} (i : Idx Δ₂ t) (v : t.Denote C),
      Held.OKV σ₁ v (V.held i) → Held.OKV σ₀ v (W.held i))
    (h : W.afterT m σ₀ p) : U.afterT m σ₀ (fun σ₁ => V.afterT m σ₁ p) := by
  refine Upd.afterT_intro (fun e he => ?_) fun g₁ σ₁ hl₁ hH₁ => ?_
  · obtain ⟨e', he'⟩ := herr e he
    exact h.of_error he'
  · refine Upd.afterT_intro (fun e he => h.of_error ((hglob g₁ σ₁ hl₁).trans he))
      fun g₂ σ₂ hl₂ hH₂ => h.of_lands (g := g₂) ?_ (hH₁.trans hH₂)
    refine ⟨(hglob g₁ σ₁ hl₁).trans hl₂.1, hl₂.2.1, fun i => ?_⟩
    rw [Held.OKT_iff_OKV]
    exact hheld g₁ σ₁ hl₁ i _ ((Held.OKT_iff_OKV _ _ _ _).1 (hl₂.2.2 i))

/-- `U` gives `U'`'s `afterT` where `U` lands only where `U'` does, and
`m.onHalt` holds where `U` halts and `U'`'s `afterT` holds. -/
theorem Upd.afterT_of_lands {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U U' : Upd C Γ Δ}
    {p : State C Δ → Prop} (he : ∀ e, U.globT σ₀ = .error e → U'.afterT m σ₀ p → m.onHalt)
    (hl : ∀ g σ', U.Lands σ₀ g σ' → U'.Lands σ₀ g σ') (h : U'.afterT m σ₀ p) :
    U.afterT m σ₀ p :=
  Upd.afterT_intro (fun e hU => he e hU h) fun _ _ hL hH => h.of_lands (hl _ _ hL) hH

/-- Landing on `σ'` from its two parts: the global part, and what each
local holds as a value. -/
theorem Upd.lands_of {Δ : Ctx} {σ₀ : State C Γ} {U U' : Upd C Γ Δ}
    (hg : ∀ g, U.globT σ₀ = .ok g → U'.globT σ₀ = .ok g)
    (hh : ∀ {t : LTy} (i : Idx Δ t) (v : t.Denote C), Held.OKV σ₀ v (U.held i) →
      Held.OKV σ₀ v (U'.held i))
    {g : Semantics.State} {σ' : State C Δ} (hL : U.Lands σ₀ g σ') : U'.Lands σ₀ g σ' :=
  ⟨hg g hL.1, hL.2.1, fun i => (Held.OKT_iff_OKV _ _ _ _).2
    (hh i _ ((Held.OKT_iff_OKV _ _ _ _).1 (hL.2.2 i)))⟩

/-! ### The state an update leaves, by constructor -/

theorem State.globE_drop {Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) : (σ.drop h).globE = σ.globE :=
  rfl

theorem State.globE_thin {Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) : (σ.thin h).globE = σ.globE :=
  rfl

theorem State.globE_push {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) :
    (σ.push v).globE = σ.globE := rfl

theorem State.globE_setLocal {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).globE = σ.globE := rfl

theorem State.getE_drop {Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) {t : LTy} (i : Idx Γ t) :
    (σ.drop h).getE i = σ.getE (i.ext h) := by
  obtain ⟨st, H, hp, env, nt, sb, tx⟩ := σ
  show LTy.TDenote.erase t (TEnv.get i (TEnv.drop h env)) = LTy.TDenote.erase t (TEnv.get (i.ext h) env)
  congr 1
  induction h with
  | refl => rfl
  | push h ih => exact ih env.2

theorem State.getE_thin {Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) {t : LTy} (i : Idx Γ t) :
    (σ.thin h).getE i = σ.getE (i.wk h) := by
  obtain ⟨st, H, hp, env, nt, sb, tx⟩ := σ
  show LTy.TDenote.erase t (TEnv.get i (TEnv.thin h env)) = LTy.TDenote.erase t (TEnv.get (i.wk h) env)
  congr 1
  induction h with
  | refl => rfl
  | keep h ih =>
    cases i with
    | here => rfl
    | there i => exact ih i env.2
  | drop h ih => exact ih i env.2

theorem State.getE_push_here {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) :
    (σ.push v).getE .here = LTy.TDenote.erase t v := rfl

theorem State.getE_push_there {t u : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) (i : Idx Γ u) :
    (σ.push v).getE i.there = σ.getE i := rfl

/-- `{}` lands on the state it is applied in. -/
theorem Upd.lands_nil (σ : State C Γ) : (Upd.nil : Upd C Γ Γ).Lands σ σ.globE σ :=
  ⟨rfl, rfl, fun _ => rfl⟩

/-- A scope's end lands on the state with its locals popped. -/
theorem Upd.lands_pop_nil {Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) :
    (Upd.pop .nil h : Upd C Δ Γ).Lands σ σ.globE (σ.drop h) :=
  ⟨rfl, rfl, fun i => State.getE_drop h σ i⟩

/-- A thinning lands on the state with its dropped locals gone. -/
theorem Upd.lands_drop_nil {Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) :
    (Upd.drop .nil h : Upd C Δ Γ).Lands σ σ.globE (σ.thin h) :=
  ⟨rfl, rfl, fun i => State.getE_thin h σ i⟩

/-- A declaration after an update lands on the state it lands on, the
declared local pushed. -/
theorem Upd.lands_decl {Δ : Ctx} {U : Upd C Γ Δ} {σ₀ : State C Γ} {g : Semantics.State}
    {σ' : State C Δ} (hL : U.Lands σ₀ g σ') (x : Var) {t : LTy} {r : Rhs C Γ t}
    {v : t.TDenote C σ'.H} (hr : r.evalT σ₀ = .ok (LTy.TDenote.erase t v)) :
    (U.decl x r).Lands σ₀ g (σ'.push v) := by
  refine ⟨?_, hL.2.1, fun i => ?_⟩
  · show (do let g' ← U.globT σ₀; let _ ← r.evalT σ₀; pure g') = _
    rw [hL.1, hr]; rfl
  · cases i with
    | here => exact hr
    | there j => exact hL.2.2 j

/-- A declaration whose right-hand side halts halts. -/
theorem Upd.globT_decl_error {Δ : Ctx} {U : Upd C Γ Δ} {σ₀ : State C Γ} {g : Semantics.State}
    (hU : U.globT σ₀ = .ok g) (x : Var) {t : LTy} {r : Rhs C Γ t} {e : Halt}
    (hr : r.evalT σ₀ = .error e) : (U.decl x r).globT σ₀ = .error e := by
  show (do let g' ← U.globT σ₀; let _ ← r.evalT σ₀; pure g') = _
  rw [hU, hr]; rfl

theorem State.getE_setLocal_self {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).getE i = LTy.TDenote.erase t v := by
  show LTy.TDenote.erase t (TEnv.get i (TEnv.set i v σ.env)) = _
  rw [TEnv.get_set]

theorem State.getE_setLocal_other {t u : LTy} (σ : State C Γ) (i : Idx Γ t) (j : Idx Γ u)
    (h : i.toNat ≠ j.toNat) (v : t.TDenote C σ.H) : (σ.setLocal i v).getE j = σ.getE j := by
  show LTy.TDenote.erase u (TEnv.get j (TEnv.set i v σ.env)) = _
  rw [TEnv.get_set_ne i j v σ.env h]

/-- A local set after an update lands on the state it lands on, the local
set. -/
theorem Upd.lands_snoc_local {Δ : Ctx} {U : Upd C Γ Δ} {σ₀ : State C Γ} {g : Semantics.State}
    {σ' : State C Δ} (hL : U.Lands σ₀ g σ') {t : LTy} (i : Idx Δ t) {r : Rhs C Γ t}
    {v : t.TDenote C σ'.H} (hr : r.evalT σ₀ = .ok (LTy.TDenote.erase t v)) :
    (U.snoc (.local i r)).Lands σ₀ g (σ'.setLocal i v) := by
  refine ⟨?_, hL.2.1, fun j => ?_⟩
  · show (do let g' ← U.globT σ₀; (UpdElem.local i r).globT σ₀ g') = _
    rw [hL.1]
    show (do let _ ← r.evalT σ₀; pure g) = _
    rw [hr]; rfl
  · show Held.OKT σ₀ (σ'.setLocal i v) j (Subst.set (Upd.held U) i r j)
    unfold Subst.set
    split
    · rename_i hij
      obtain rfl := Idx.ty_eq_of_toNat hij
      obtain rfl := Idx.toNat_inj i j hij
      show r.evalT σ₀ = .ok ((σ'.setLocal i v).getE i)
      rw [State.getE_setLocal_self]
      exact hr
    · rename_i hij
      rw [Held.OKT_iff_OKV, State.getE_setLocal_other σ' i j hij]
      exact (Held.OKT_iff_OKV _ _ _ _).1 (hL.2.2 j)

end Kit

/-! ## The typed state's readers, by position

What `sol_close`'s kit (`Calculus/CloseScoped.lean`) and the decision
procedure read a typed state by: its global part (`State.globE`) and its
locals (`State.getE`) after a push, a set, an anonymisation, a havoc, a pop
and a thinning. -/

section CloseKit

variable {Γ : Ctx}

theorem State.getE_setLocal_same {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).getE i = LTy.TDenote.erase t v := by
  show LTy.TDenote.erase t (TEnv.get i (TEnv.set i v σ.env)) = _
  rw [TEnv.get_set]
theorem State.getE_setLocal_ne {t u : LTy} (σ : State C Γ) (i : Idx Γ t) (j : Idx Γ u)
    (h : i.toNat ≠ j.toNat) (v : t.TDenote C σ.H) : (σ.setLocal i v).getE j = σ.getE j := by
  show LTy.TDenote.erase u (TEnv.get j (TEnv.set i v σ.env)) = _
  rw [TEnv.get_set_ne i j v σ.env h]
theorem State.anon_nil (σ : State C Γ) (b : (x : (t : LTy) × Idx Γ t) → x.1.TDenote C σ.H) :
    σ.anon [] b = σ := rfl
theorem State.anon_cons (σ : State C Γ) (x : (t : LTy) × Idx Γ t)
    (xs : List ((t : LTy) × Idx Γ t)) (b : (x : (t : LTy) × Idx Γ t) → x.1.TDenote C σ.H) :
    σ.anon (x :: xs) b = (σ.setLocal x.2 (b x)).anon xs b := rfl
theorem State.globE_havoc (σ : State C Γ) (st : Storage C) (nt : List (Int × Int)) :
    (σ.havoc st nt).globE = σ.globE.havoc st.erase nt := rfl
theorem State.getE_havoc {t : LTy} (σ : State C Γ) (st : Storage C) (nt : List (Int × Int))
    (i : Idx Γ t) : (σ.havoc st nt).getE i = σ.getE i := rfl

/-! ### Where an update lands, computed

The global part and the locals an update leaves, as values: `Upd.applyV`
computes the pair a landed state's `State.globE` and `State.getE` read
(`Upd.lands_iff_applyV`), each right-hand side read once in the state the
update is applied in.  The closer reads an update's rest by it
(`CloseS.holds_upd`), and the decision procedure relates its symbols to
it. -/

/-- A local set. -/
def Locs.set {Δ : Ctx} (ℓ : Locs C Δ) {t : LTy} (i : Idx Δ t) (v : t.Denote C) : Locs C Δ :=
  fun _ j => if h : i.toNat = j.toNat then Idx.ty_eq_of_toNat h ▸ v else ℓ _ j

/-- A suffix popped. -/
def Locs.drop {Δ Δ' : Ctx} (h : Ext Δ' Δ) (ℓ : Locs C Δ) : Locs C Δ' := fun _ j => ℓ _ (j.ext h)

/-- A frame thinned. -/
def Locs.thin {Δ Δ' : Ctx} (h : Thin Δ' Δ) (ℓ : Locs C Δ) : Locs C Δ' := fun _ j => ℓ _ (j.wk h)

theorem Locs.set_same {Δ : Ctx} (ℓ : Locs C Δ) {t : LTy} (i : Idx Δ t) (v : t.Denote C) :
    ℓ.set i v t i = v := by
  unfold Locs.set
  rw [dif_pos rfl]

theorem Locs.set_ne {Δ : Ctx} (ℓ : Locs C Δ) {t u : LTy} (i : Idx Δ t) (j : Idx Δ u)
    (h : i.toNat ≠ j.toNat) (v : t.Denote C) : ℓ.set i v u j = ℓ u j := by
  unfold Locs.set
  rw [dif_neg h]

/-- One element applied to a global part and locals, its right-hand sides
read in `σ₀`. -/
def UpdElem.applyV {Δ : Ctx} (σ₀ : State C Γ) :
    UpdElem C Γ Δ → Semantics.State → Locs C Δ → Res (Semantics.State × Locs C Δ)
  | .local i r, g, ℓ => do pure (g, ℓ.set i (← r.evalT σ₀))
  | .storage s, g, ℓ => do pure (← (UpdElem.storage s : UpdElem C Γ Δ).globT σ₀ g, ℓ)
  | .memory m, g, ℓ => do pure (← (UpdElem.memory m : UpdElem C Γ Δ).globT σ₀ g, ℓ)
  | .selfBalance op a, g, ℓ => do
    pure (← (UpdElem.selfBalance op a : UpdElem C Γ Δ).globT σ₀ g, ℓ)
  | .net r op a, g, ℓ => do pure (← (UpdElem.net r op a : UpdElem C Γ Δ).globT σ₀ g, ℓ)
  | .pay r a, g, ℓ => do pure (← (UpdElem.pay r a : UpdElem C Γ Δ).globT σ₀ g, ℓ)
  | .netMt r a, g, ℓ => do pure (← (UpdElem.netMt r a : UpdElem C Γ Δ).globT σ₀ g, ℓ)
  | .setBalance a, g, ℓ => do pure (← (UpdElem.setBalance a : UpdElem C Γ Δ).globT σ₀ g, ℓ)

/-- **What an update applied in `σ₀` leaves**: the global part and the
locals' values. -/
def Upd.applyV (σ₀ : State C Γ) : {Δ : Ctx} → Upd C Γ Δ → Res (Semantics.State × Locs C Δ)
  | _, .nil => pure (σ₀.globE, σ₀.loc)
  | _, .snoc U e => do let p ← U.applyV σ₀; e.applyV σ₀ p.1 p.2
  | _, .decl U _ r => do
    let p ← U.applyV σ₀
    let v ← r.evalT σ₀
    pure (p.1, p.2.push v)
  | _, .pop U h => do let p ← U.applyV σ₀; pure (p.1, p.2.drop h)
  | _, .drop U h => do let p ← U.applyV σ₀; pure (p.1, p.2.thin h)


theorem Held.OKV.unique {t : LTy} {σ₀ : State C Γ} {v w : t.Denote C} :
    (x : Held C Γ t) → Held.OKV σ₀ v x → Held.OKV σ₀ w x → v = w
  | .pos _, h₁, h₂ => h₁.trans h₂.symm
  | .rhs _, h₁, h₂ => Except.ok.inj (h₁.symm.trans h₂)

private theorem elem_applyV_ok {Δ : Ctx} {σ₀ : State C Γ} (e : UpdElem C Γ Δ)
    {g g' : Semantics.State} {ℓ ℓ' : Locs C Δ} (h : e.applyV σ₀ g ℓ = .ok (g', ℓ')) :
    e.globT σ₀ g = .ok g' ∧
      ((∃ (u : LTy) (i : Idx Δ u) (r : Rhs C Γ u) (v : u.Denote C), e = .local i r ∧
        r.evalT σ₀ = .ok v ∧ ℓ' = ℓ.set i v) ∨ ((∀ (u : LTy) (i : Idx Δ u) (r : Rhs C Γ u),
          e ≠ .local i r) ∧ ℓ' = ℓ)) := by
  cases e with
  | «local» i r =>
    obtain ⟨v, hv, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    cases h
    refine ⟨?_, .inl ⟨_, i, r, v, rfl, hv, rfl⟩⟩
    show (do let _ ← r.evalT σ₀; pure g) = _
    rw [hv]; rfl
  | storage _ | memory _ | selfBalance _ _ | net _ _ _ | pay _ _ | netMt _ _ | setBalance _ =>
    obtain ⟨g₁, hg, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    cases h
    exact ⟨hg, .inr ⟨fun _ _ _ he => UpdElem.noConfusion he, rfl⟩⟩

/-- **What `applyV` computes is the global part `globT` computes and, in
each local, what `Upd.held` says.** -/
theorem Upd.applyV_ok {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    {g : Semantics.State} → {ℓ : Locs C Δ} → U.applyV σ₀ = .ok (g, ℓ) →
    U.globT σ₀ = .ok g ∧ ∀ {t : LTy} (i : Idx Δ t), Held.OKV σ₀ (ℓ t i) (U.held i)
  | _, .nil, g, ℓ, h => by
    cases h
    exact ⟨rfl, fun _ => rfl⟩
  | _, .snoc U e, g, ℓ, h => by
    obtain ⟨p, hp, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    obtain ⟨g₁, ℓ₁⟩ := p
    obtain ⟨hg₁, hh₁⟩ := Upd.applyV_ok U hp
    obtain ⟨hg, hl⟩ := elem_applyV_ok e h
    refine ⟨?_, ?_⟩
    · show (do e.globT σ₀ (← U.globT σ₀)) = _
      rw [hg₁]; exact hg
    · intro t i
      rcases hl with ⟨u, k, r, v, rfl, hv, rfl⟩ | ⟨hne, rfl⟩
      · show Held.OKV σ₀ _ (Subst.set (Upd.held U) k r i)
        unfold Subst.set
        split
        · rename_i hki
          obtain rfl := Idx.ty_eq_of_toNat hki
          obtain rfl := Idx.toNat_inj k i hki
          show r.evalT σ₀ = .ok (ℓ₁.set k v _ k)
          rw [Locs.set_same]; exact hv
        · rename_i hki
          rw [Locs.set_ne ℓ₁ k i hki]
          exact hh₁ i
      · have hheld : (Upd.snoc U e).held i = U.held i := by
          cases e with
          | «local» k r => exact absurd rfl (hne _ k r)
          | _ => rfl
        rw [hheld]
        exact hh₁ i
  | _, .decl U _ r, g, ℓ, h => by
    obtain ⟨p, hp, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    obtain ⟨v, hv, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    obtain ⟨g₁, ℓ₁⟩ := p
    cases h
    obtain ⟨hg₁, hh₁⟩ := Upd.applyV_ok U hp
    refine ⟨?_, ?_⟩
    · show (do let g ← U.globT σ₀; let _ ← r.evalT σ₀; pure g) = _
      rw [hg₁, hv]; rfl
    · intro t i
      cases i with
      | here => exact hv
      | there j => exact hh₁ j
  | _, .pop U hx, g, ℓ, h => by
    obtain ⟨p, hp, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    obtain ⟨g₁, ℓ₁⟩ := p
    cases h
    obtain ⟨hg₁, hh₁⟩ := Upd.applyV_ok U hp
    exact ⟨hg₁, fun i => hh₁ (i.ext hx)⟩
  | _, .drop U hx, g, ℓ, h => by
    obtain ⟨p, hp, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    obtain ⟨g₁, ℓ₁⟩ := p
    cases h
    obtain ⟨hg₁, hh₁⟩ := Upd.applyV_ok U hp
    exact ⟨hg₁, fun i => hh₁ (i.wk hx)⟩

/-- Where `globT` returns, so does `applyV`. -/
theorem Upd.applyV_of_globT {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    {g : Semantics.State} → U.globT σ₀ = .ok g → ∃ ℓ, U.applyV σ₀ = .ok (g, ℓ)
  | _, .nil, g, h => by cases h; exact ⟨_, rfl⟩
  | _, .snoc U e, g, h => by
    obtain ⟨g₁, hg₁, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    obtain ⟨ℓ₁, hℓ₁⟩ := Upd.applyV_of_globT U hg₁
    show ∃ ℓ, (do let p ← U.applyV σ₀; e.applyV σ₀ p.1 p.2) = _
    rw [hℓ₁, Solidity.SemanticsProperties.Res.ok_bind]
    cases e with
    | «local» i r =>
      obtain ⟨v, hv, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
      cases h
      exact ⟨_, by show (do pure (_, ℓ₁.set i (← r.evalT σ₀))) = _; rw [hv]; rfl⟩
    | _ => exact ⟨ℓ₁, by simp only [UpdElem.applyV, h]; rfl⟩
  | _, .decl U _ r, g, h => by
    obtain ⟨g₁, hg₁, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    obtain ⟨v, hv, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    cases h
    obtain ⟨ℓ₁, hℓ₁⟩ := Upd.applyV_of_globT U hg₁
    exact ⟨_, by
      show (do let p ← U.applyV σ₀; let v ← r.evalT σ₀; pure (p.1, p.2.push v)) = _
      rw [hℓ₁, hv]; rfl⟩
  | _, .pop U hx, g, h => by
    obtain ⟨ℓ₁, hℓ₁⟩ := Upd.applyV_of_globT U h
    exact ⟨_, by show (do let p ← U.applyV σ₀; pure (p.1, p.2.drop hx)) = _; rw [hℓ₁]; rfl⟩
  | _, .drop U hx, g, h => by
    obtain ⟨ℓ₁, hℓ₁⟩ := Upd.applyV_of_globT U h
    exact ⟨_, by show (do let p ← U.applyV σ₀; pure (p.1, p.2.thin hx)) = _; rw [hℓ₁]; rfl⟩

/-- **Landing, computed**: `U` lands on `σ'` exactly where `applyV`
returns `σ'`'s global part and locals. -/
theorem Upd.lands_iff_applyV {Δ : Ctx} {σ₀ : State C Γ} {U : Upd C Γ Δ} {g : Semantics.State}
    {σ' : State C Δ} : U.Lands σ₀ g σ' ↔
      ∃ ℓ, U.applyV σ₀ = .ok (g, ℓ) ∧ σ'.globE = g ∧ ∀ {t : LTy} (i : Idx Δ t), σ'.getE i = ℓ t i := by
  constructor
  · rintro ⟨hg, hσ, hh⟩
    obtain ⟨ℓ, hℓ⟩ := Upd.applyV_of_globT U hg
    refine ⟨ℓ, hℓ, hσ, fun i => ?_⟩
    have hv := (Upd.applyV_ok U hℓ).2 i
    have ho : Held.OKV σ₀ (σ'.getE i) (U.held i) := by
      have := hh i
      revert this
      cases U.held i with
      | pos j => exact id
      | rhs r => exact id
    exact Held.OKV.unique _ ho hv
  · rintro ⟨ℓ, hℓ, hσ, he⟩
    obtain ⟨hg, hh⟩ := Upd.applyV_ok U hℓ
    refine ⟨hg, hσ, fun i => ?_⟩
    have hv := hh i
    rw [← he i] at hv
    revert hv
    cases U.held i with
    | pos j => exact id
    | rhs r => exact id

/-- **`afterT`, computed**: `p` of every typed state with the global part
and the locals `applyV` returns, or `m.onHalt` where it halts. -/
theorem Upd.afterT_applyV {Δ : Ctx} (m : Modality) (σ₀ : State C Γ) (U : Upd C Γ Δ)
    (p : State C Δ → Prop) :
    U.afterT m σ₀ p ↔ m.afterC (fun q => ∀ σ' : State C Δ, σ'.globE = q.1 →
      (∀ {t : LTy} (i : Idx Δ t), σ'.getE i = q.2 t i) → σ₀.H <+: σ'.H → p σ') (U.applyV σ₀) := by
  unfold Upd.afterT
  split
  · rename_i e he
    cases ha : U.applyV σ₀ with
    | error => exact Iff.rfl
    | ok q =>
      obtain ⟨g, ℓ⟩ := q
      rw [(Upd.applyV_ok U ha).1] at he; cases he
  · rename_i g hg
    obtain ⟨ℓ, hℓ⟩ := Upd.applyV_of_globT U hg
    rw [hℓ]
    show (∀ σ' : State C Δ, U.Lands σ₀ g σ' → _) ↔ (∀ σ' : State C Δ, σ'.globE = g → _)
    refine forall_congr' fun σ' => ⟨fun h hσ he hH => h (Upd.lands_iff_applyV.2 ⟨ℓ, hℓ, hσ, he⟩) hH,
      fun h hl hH => ?_⟩
    obtain ⟨ℓ', hℓ', hσ, he⟩ := Upd.lands_iff_applyV.1 hl
    rw [hℓ] at hℓ'
    cases hℓ'
    exact h hσ he hH

theorem State.loc_apply (σ : State C Γ) {t : LTy} (i : Idx Γ t) : σ.loc t i = σ.getE i := rfl



theorem TEnv.get_thin_wk {H : HTy} : {Δ Δ' : Ctx} → (h : Thin Δ' Δ) → {t : LTy} → (j : Idx Δ' t) →
    (e : TEnv C H Δ) → TEnv.get j (TEnv.thin h e) = TEnv.get (j.wk h) e
  | _, _, .refl, _, _, _ => rfl
  | _, _, .keep _, _, .here, _ => rfl
  | _, _, .keep h, _, .there j, e => TEnv.get_thin_wk h j e.2
  | _, _, .drop h, _, j, e => TEnv.get_thin_wk h j e.2

theorem State.loc_push {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) :
    (σ.push v).loc = σ.loc.push (LTy.TDenote.erase t v) := by
  funext u j
  cases j <;> rfl
theorem State.loc_drop {Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) : (σ.drop h).loc = σ.loc.drop h := by
  funext u j
  exact State.getE_drop h σ j
theorem State.loc_thin {Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) : (σ.thin h).loc = σ.loc.thin h := by
  funext u j
  show LTy.TDenote.erase u (TEnv.get j (TEnv.thin h σ.env)) = _
  rw [TEnv.get_thin_wk]
  rfl
theorem State.loc_setLocal {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).loc = σ.loc.set i (LTy.TDenote.erase t v) := by
  funext u j
  show (σ.setLocal i v).getE j = _
  by_cases h : i.toNat = j.toNat
  · obtain rfl := Idx.ty_eq_of_toNat h
    obtain rfl := Idx.toNat_inj i j h
    rw [State.getE_setLocal_same, Locs.set_same]
  · rw [State.getE_setLocal_ne σ i j h, Locs.set_ne _ i j h]
    rfl

open Semantics (bind_ok_inv) in
/-- **The term bridge** (`Theory/Bridge/Denote.lean`): a term's denotation
agrees with its reading in a typed state wherever the reading returns. -/
theorem _root_.Solidity.Tm.denoteT_evalT (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) →
    Srt.Bridge s (t.denoteT σ) (t.evalT σ)
  | _, .pvV _ => by intro x h; cases h; rfl
  | _, .pvP i => by
    intro r segs h
    have h' : σ.aliasPathT i = .ok (r, segs) := h
    simp only [Tm.denoteT, h']
  | _, .pvS _ => by intro τ h; cases h; exact StValue.Equiv.refl _
  | _, .pvI _ => trivial
  | _, .netOf i a => by
    intro x h
    obtain ⟨va, ha, h⟩ := bind_ok_inv h
    obtain ⟨n, hn, h⟩ := bind_ok_inv h
    cases h
    cases va with
    | bool => cases hn
    | int n' =>
      cases hn
      simp only [Tm.denoteT, Tm.denoteT_evalT σ a _ ha]
  | _, .app0 o => Op0.denote_eval o
  | _, .app1 o _ a => Op1.denote_eval o (Tm.denoteT_evalT σ a)
  | _, .app2 o a b => Op2.denote_eval o (Tm.denoteT_evalT σ a) (Tm.denoteT_evalT σ b)
  | _, .app3 o a b c =>
    Op3.denote_eval o (Tm.denoteT_evalT σ a) (Tm.denoteT_evalT σ b) (Tm.denoteT_evalT σ c)


end CloseKit

end Solidity
