import Solidity.Calculus.Step
import Solidity.Semantics.Erased
import Solidity.Update
import Solidity.Theory.Observe
import Solidity.Typing.Soundness
import Solidity.Semantics.RunFrame
import Solidity.Theory.Bridge.Denote

/-!
# Terms and updates read in a state; where an update lands

What `holds` (`Calculus/Logic.lean`) reads a term and an update by.

* The `EState` readers (`Tm.eval`, `Tm.denote`, `Rhs.eval`, `Upd.apply`):
  a term on an erased state, an update applied to one (decision U1,
  W9.6.0).  They stay as twins until `EState` goes (W9.7.3).
* The typed readers (`Tm.evalT`, `Tm.denoteT`, `Rhs.evalT`): the same on
  the typed state, its global part erased (`State.globE`), a local read by
  its position and erased at its type (`State.getE`); each equal to its twin
  on the erasure (`Tm.evalT_eq`, …).
* What an update leaves in each local (`Upd.held`: a local it kept, or the
  right-hand side it last wrote), and where it lands (decision U2, chosen at
  W9.7): `Upd.Lands σ₀ U g σ'`, `U`'s global part `g` (`Upd.globT`) is
  `σ'`'s and each local of `σ'` holds what `Upd.held` says, read in `σ₀`.
  The states it lands on are the typed states that erase to what
  `Upd.apply` computes (`Upd.lands_iff`), so `Upd.afterT`, `holds`' update
  clause, is the erased reading (`Upd.afterT_iff`).
-/

namespace Solidity
open Semantics (Value SVal MVal Seg Halt Res lookupBy setBy allocDefault applyUnOp)
open Solidity (evalBinop unopCheck)
open Theory Theory.StValue
open Solidity (Srt Op0 Op1 Op2 Op3 Modality IntOp)

variable {C : Contract}

/-! ## Terms -/

section Terms

variable {Γ : Ctx}

/-- A term read by the interpreter in `σ`: a local by its position, a symbol
on the global part. -/
def Tm.eval (σ : EState C Γ) : {s : Srt} → Tm C Γ s → s.Ev
  | _, .pvV i => pure (Env.get i σ.env)
  | _, .pvP i => aliasPath σ i
  | _, .pvS i => pure { σ.glob with storage := Env.get i σ.env }
  | _, .pvI i => memRef σ i
  | _, .netOf i a => do
    let l : List (Int × Int) := Env.get i σ.env
    pure (.int ((lookupBy (← (← a.eval σ).asInt) l).getD 0))
  | _, .app0 o => o.eval σ.glob
  | _, .app1 o _ a => o.eval σ.glob (a.eval σ)
  | _, .app2 o a b => o.eval σ.glob (a.eval σ) (b.eval σ)
  | _, .app3 o a b c => o.eval σ.glob (a.eval σ) (b.eval σ) (c.eval σ)

/-- A term in the Theory, over `State.abs σ.glob` (`Update.lean`'s
`Tm.denote`). -/
def Tm.denote (σ : EState C Γ) : {s : Srt} → Tm C Γ s → s.Den
  | _, .pvV i => .prim (Env.get i σ.env)
  | _, .pvP i => match aliasPath σ i with
    | .ok (r, segs) => rootPath r segs
    | .error _ => []
  | _, .pvS i => SVal.abs.fields (Env.get i σ.env)
  | _, .pvI _ => ()
  | _, .netOf i a => match a.denote σ with
    | .prim (.int n) => .prim (.int ((lookupBy n (Env.get i σ.env : List (Int × Int))).getD 0))
    | _ => .st .mtSt
  | _, .app0 o => o.denote σ.glob
  | _, .app1 o _ a => o.denote σ.glob (a.denote σ)
  | _, .app2 o a b => o.denote σ.glob (a.eval σ) (b.eval σ) (a.denote σ) (b.denote σ)
  | _, .app3 o a b c => o.denote (a.denote σ) (b.denote σ) (c.denote σ)

end Terms

/-! ## Updates -/

section Updates

/-- A scope's locals dropped by a thinning: the ones `Γ` keeps. -/
def Env.thin : {Γ Δ : Ctx} → Thin Γ Δ → Env C Δ → Env C Γ
  | _, _, .refl, e => e
  | _, _, .keep h, e => (e.1, Env.thin h e.2)
  | _, _, .drop h, e => Env.thin h e.2

/-- A state's locals thinned. -/
def EState.thin {Γ Δ : Ctx} (h : Thin Γ Δ) (σ : EState C Δ) : EState C Γ :=
  σ.withEnv (Env.thin h σ.env)

variable {Γ : Ctx}

/-- What a local is set to, read in `σ₀`. -/
def Rhs.eval (σ₀ : EState C Γ) : {t : LTy} → Rhs C Γ t → Res (t.Denote C)
  | _, .val t => t.eval σ₀
  | _, .path p => do pure (some (← p.eval σ₀))
  | _, .unset => pure none
  | _, .mref i => do pure (some (← i.eval σ₀))
  | _, .store s => do pure (← s.eval σ₀).storage
  | _, .saveNet => pure σ₀.net
  | _, .saveNetMt => pure []

/-- One assigning element: its right-hand sides read in `σ₀`, the write
into `τ` (`Update.lean`'s `UpdElem.write`). -/
def UpdElem.write {Δ : Ctx} (σ₀ : EState C Γ) : UpdElem C Γ Δ → EState C Δ → Res (EState C Δ)
  | .local i r, τ => do pure (τ.setLocal i (← r.eval σ₀))
  | .storage s, τ => do
    let st := (← s.eval σ₀).storage
    pure (τ.withGlob { τ.glob with storage := st })
  | .memory m, τ => do
    let μ ← m.eval σ₀
    pure (τ.withGlob { τ.glob with heap := μ.heap, nextId := μ.nextId })
  | .selfBalance op a, τ => do
    let amt ← (← a.eval σ₀).asInt
    pure (τ.withGlob { τ.glob with selfBalance := op.apply σ₀.selfBalance amt })
  | .net r op a, τ => do
    let addr ← (← r.eval σ₀).asInt
    let amt ← (← a.eval σ₀).asInt
    pure (τ.withGlob { τ.glob with net := setBy addr (op.apply (τ.glob.getNet addr) amt) τ.net })
  | .pay r a, τ => do
    let addr ← (← r.eval σ₀).asInt
    let amt ← (← a.eval σ₀).asInt
    if amt < 0 then .error .revert
    else pure (τ.withGlob { τ.glob with
      net := if addr = σ₀.tx.selfAddress then τ.net else setBy addr (τ.glob.getNet addr - amt) τ.net })
  | .netMt r a, τ => do
    let addr ← (← r.eval σ₀).asInt
    let amt ← (← a.eval σ₀).asInt
    pure (τ.withGlob { τ.glob with net := [(addr, amt)] })
  | .setBalance a, τ => do
    let amt ← (← a.eval σ₀).asInt
    pure (τ.withGlob { τ.glob with selfBalance := amt })

/-- The state an update applied in `σ₀` leaves, in the context its type
says. -/
def Upd.apply (σ₀ : EState C Γ) : {Δ : Ctx} → Upd C Γ Δ → Res (EState C Δ)
  | _, .nil => pure σ₀
  | _, .snoc U e => do e.write σ₀ (← U.apply σ₀)
  | _, .decl U _ r => do
    let τ ← U.apply σ₀
    pure (τ.push (← r.eval σ₀))
  | _, .pop U h => (U.apply σ₀).map (EState.drop h)
  | _, .drop U h => (U.apply σ₀).map (EState.thin h)

end Updates

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

/-! ## What an update leaves, on the erasure -/

section HeldE

variable {Γ : Ctx}

/-- What `U` left in a local, read in the states before (`σ₀`) and after
(`σ₁`). -/
def Held.OK {Δ : Ctx} (σ₀ : EState C Γ) (σ₁ : EState C Δ) {t : LTy} (i : Idx Δ t) :
    Held C Γ t → Prop
  | .pos j => Env.get i σ₁.env = Env.get j σ₀.env
  | .rhs r => r.eval σ₀ = .ok (Env.get i σ₁.env)

theorem Env.get_set_other {Δ : Ctx} {t u : LTy} (i : Idx Δ t) (j : Idx Δ u) (h : i.toNat ≠ j.toNat)
    (v : t.Denote C) (e : Env C Δ) : Env.get j (Env.set i v e) = Env.get j e := by
  induction i with
  | here =>
    cases j with
    | here => exact absurd rfl h
    | there j => rfl
  | there i ih =>
    cases j with
    | here => rfl
    | there j => exact ih j (fun h' => h (congrArg (· + 1) h')) v e.2

theorem Env.get_drop {Δ Δ' : Ctx} {t : LTy} (h : Ext Δ' Δ) (j : Idx Δ' t) (e : Env C Δ) :
    Env.get j (Env.drop h e) = Env.get (j.ext h) e := by
  induction h with
  | refl => rfl
  | push h ih => exact ih e.2

theorem Env.get_thin : {Δ Δ' : Ctx} → (h : Thin Δ' Δ) → {t : LTy} → (j : Idx Δ' t) → (e : Env C Δ) →
    Env.get j (Env.thin h e) = Env.get (j.wk h) e
  | _, _, .refl, _, _, _ => rfl
  | _, _, .keep _, _, .here, _ => rfl
  | _, _, .keep h, _, .there j, e => Env.get_thin h j e.2
  | _, _, .drop h, _, j, e => Env.get_thin h j e.2

/-- A local read alike in two states keeps what it holds. -/
theorem Held.OK.congr {Δ Δ' : Ctx} {σ₀ : EState C Γ} {σ₁ : EState C Δ} {σ₁' : EState C Δ'} {t : LTy}
    {i : Idx Δ t} {i' : Idx Δ' t} (he : Env.get i' σ₁'.env = Env.get i σ₁.env) :
    (x : Held C Γ t) → Held.OK σ₀ σ₁ i x → Held.OK σ₀ σ₁' i' x
  | .pos _, h => he.trans h
  | .rhs _, h => h.trans (congrArg _ he.symm)

/-- **What `U` leaves in each local** is what `Upd.held` says. -/
theorem Upd.held_ok {σ₀ : EState C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) → {σ₁ : EState C Δ} →
    U.apply σ₀ = .ok σ₁ → ∀ {t : LTy} (i : Idx Δ t), Held.OK σ₀ σ₁ i (U.held i)
  | _, .nil, _, h, _, i => by cases h; rfl
  | _, .snoc U e, σ₁, h, t, i => by
    change (do e.write σ₀ (← U.apply σ₀)) = .ok σ₁ at h
    obtain ⟨τ, hτ, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    cases e with
    | «local» k r =>
      change (do pure (τ.setLocal k (← r.eval σ₀))) = .ok σ₁ at h
      obtain ⟨v, hv, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
      cases h
      show Held.OK σ₀ _ i (Subst.set (Upd.held U) k r i)
      unfold Subst.set
      split
      · rename_i hki
        obtain rfl := Idx.ty_eq_of_toNat hki
        obtain rfl := Idx.toNat_inj k i hki
        show r.eval σ₀ = .ok (Env.get k (Env.set k v τ.env))
        rw [Env.get_set]; exact hv
      · rename_i hki
        exact Held.OK.congr (Env.get_set_other k i hki v τ.env) _ (Upd.held_ok U hτ i)
    | storage x | memory x | selfBalance op x | net r op x | pay r x | netMt r x | setBalance x =>
      have henv : σ₁.env = τ.env := by
        simp only [UpdElem.write, bind, Except.bind, pure, Except.pure] at h
        repeat' split at h
        all_goals first | (cases h; rfl) | cases h
      exact Held.OK.congr (by rw [henv]) _ (Upd.held_ok U hτ i)
  | _, .decl U _ r, σ₁, h, t, i => by
    change (do let τ ← U.apply σ₀; pure (τ.push (← r.eval σ₀))) = .ok σ₁ at h
    obtain ⟨τ, hτ, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    obtain ⟨v, hv, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    cases h
    cases i with
    | here => exact hv
    | there j => exact Held.OK.congr (σ₁ := τ) (i := j) rfl _ (Upd.held_ok U hτ j)
  | _, .pop U e, σ₁, h, t, i => by
    change (U.apply σ₀).map (EState.drop e) = .ok σ₁ at h
    cases hτ : U.apply σ₀ with
    | error => rw [hτ] at h; cases h
    | ok τ =>
      rw [hτ] at h; cases h
      exact Held.OK.congr (Env.get_drop e i τ.env) _ (Upd.held_ok U hτ (i.ext e))
  | _, .drop U e, σ₁, h, t, i => by
    change (U.apply σ₀).map (EState.thin e) = .ok σ₁ at h
    cases hτ : U.apply σ₀ with
    | error => rw [hτ] at h; cases h
    | ok τ =>
      rw [hτ] at h; cases h
      exact Held.OK.congr (Env.get_thin e i τ.env) _ (Upd.held_ok U hτ (i.wk e))

theorem Env.ext_get : {Γ : Ctx} → (e e' : Env C Γ) →
    (∀ {t : LTy} (i : Idx Γ t), Env.get i e = Env.get i e') → e = e'
  | [], (), (), _ => rfl
  | _ :: _, (a, e), (a', e'), h => by
    have h0 : a = a' := h .here
    have h1 : e = e' := Env.ext_get e e' fun i => h (.there i)
    rw [h0, h1]

end HeldE

/-! ## The typed readers

A term read on the typed state itself: the global part erased
(`State.globE`), a local by `TEnv.get`, erased at its type (`State.getE`).
Each reader equals its `EState` twin on the erasure (`Tm.evalT_eq`,
`Tm.denoteT_eq`, `Rhs.evalT_eq`): the twins go with `EState` (W9.7.3). -/

section Typed

variable {Γ : Ctx}

/-- The global part of a typed state, erased. -/
def State.globE (σ : State C Γ) : Semantics.State :=
  { storage := σ.storage.erase, heap := σ.heap.erase, nextId := σ.H.length, net := σ.net,
    selfBalance := σ.selfBalance.1, tx := σ.tx.erase }

theorem State.globE_eq (σ : State C Γ) : σ.globE = σ.erase.glob := rfl

/-- A local, erased at its type. -/
abbrev State.getE (σ : State C Γ) {t : LTy} (i : Idx Γ t) : t.Denote C :=
  LTy.TDenote.erase t (TEnv.get i σ.env)

theorem State.getE_eq (σ : State C Γ) {t : LTy} (i : Idx Γ t) :
    σ.getE i = Env.get i σ.erase.env :=
  (TEnv.get_erase i σ.env).symm

/-- The path an alias is bound to; an unset one reverts (`aliasPath`). -/
def State.aliasPathT (σ : State C Γ) {R : RefTy} (i : Idx Γ (.alias R)) :
    Res (Name × List Seg) :=
  match (TEnv.get i σ.env : Option (SRef C (.ref R))) with
  | some r => pure r.erase
  | none => .error .revert

/-- The object a memory local names; an unset one reverts (`memRef`). -/
def State.memRefT (σ : State C Γ) {R : RefTy} (i : Idx Γ (.mem R)) : Res Nat :=
  match (TEnv.get i σ.env : Option (HRef σ.H R)) with
  | some r => pure r.id
  | none => .error .revert

theorem State.aliasPathT_eq (σ : State C Γ) {R : RefTy} (i : Idx Γ (.alias R)) :
    σ.aliasPathT i = aliasPath σ.erase i := by
  unfold State.aliasPathT aliasPath
  rw [← State.getE_eq]
  dsimp only [State.getE]
  generalize (TEnv.get i σ.env : Option (SRef C (.ref R))) = x
  cases x <;> rfl

theorem State.memRefT_eq (σ : State C Γ) {R : RefTy} (i : Idx Γ (.mem R)) :
    σ.memRefT i = memRef σ.erase i := by
  unfold State.memRefT memRef
  rw [← State.getE_eq]
  dsimp only [State.getE]
  generalize (TEnv.get i σ.env : Option (HRef σ.H R)) = x
  cases x <;> rfl

/-- A term read in the typed state `σ` (`Tm.eval` on its erasure). -/
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

/-- A term in the Theory, read in the typed state `σ` (`Tm.denote` on its
erasure). -/
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

theorem Tm.evalT_eq (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) → t.evalT σ = t.eval σ.erase
  | _, .pvV i => by rw [Tm.evalT, Tm.eval, State.getE_eq]
  | _, .pvP i => State.aliasPathT_eq σ i
  | _, .pvS i => by rw [Tm.evalT, Tm.eval, State.getE_eq]; rfl
  | _, .pvI i => State.memRefT_eq σ i
  | _, .netOf i a => by rw [Tm.evalT, Tm.eval, State.getE_eq, Tm.evalT_eq σ a]
  | _, .app0 _ => rfl
  | _, .app1 o _ a => by rw [Tm.evalT, Tm.eval, Tm.evalT_eq σ a]; rfl
  | _, .app2 o a b => by rw [Tm.evalT, Tm.eval, Tm.evalT_eq σ a, Tm.evalT_eq σ b]; rfl
  | _, .app3 o a b c => by
    rw [Tm.evalT, Tm.eval, Tm.evalT_eq σ a, Tm.evalT_eq σ b, Tm.evalT_eq σ c]; rfl

theorem Tm.denoteT_eq (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) →
    t.denoteT σ = t.denote σ.erase
  | _, .pvV i => by rw [Tm.denoteT, Tm.denote, State.getE_eq]
  | _, .pvP i => by rw [Tm.denoteT, Tm.denote, State.aliasPathT_eq]
  | _, .pvS i => by rw [Tm.denoteT, Tm.denote, State.getE_eq]
  | _, .pvI _ => rfl
  | _, .netOf i a => by rw [Tm.denoteT, Tm.denote, State.getE_eq, Tm.denoteT_eq σ a]
  | _, .app0 _ => rfl
  | _, .app1 o _ a => by rw [Tm.denoteT, Tm.denote, Tm.denoteT_eq σ a]; rfl
  | _, .app2 o a b => by
    rw [Tm.denoteT, Tm.denote, Tm.denoteT_eq σ a, Tm.denoteT_eq σ b, Tm.evalT_eq σ a,
      Tm.evalT_eq σ b]; rfl
  | _, .app3 o a b c => by
    rw [Tm.denoteT, Tm.denote, Tm.denoteT_eq σ a, Tm.denoteT_eq σ b, Tm.denoteT_eq σ c]

theorem Rhs.evalT_eq (σ₀ : State C Γ) : {t : LTy} → (r : Rhs C Γ t) →
    r.evalT σ₀ = r.eval σ₀.erase
  | _, .val t => Tm.evalT_eq σ₀ t
  | _, .path p => by rw [Rhs.evalT, Rhs.eval, Tm.evalT_eq]
  | _, .unset => rfl
  | _, .mref i => by rw [Rhs.evalT, Rhs.eval, Tm.evalT_eq]
  | _, .store s => by rw [Rhs.evalT, Rhs.eval, Tm.evalT_eq]
  | _, .saveNet => rfl
  | _, .saveNetMt => rfl

end Typed

/-! ## Landing

An update applied in a typed state `σ₀` computes its global part
(`Upd.globT`) and what it leaves in each local (`Upd.held`), read in `σ₀`.
It lands on every typed state with that global part and those locals
(`Upd.Lands`): exactly the typed states that erase to what `Upd.apply`
computes on `σ₀`'s erasure (`Upd.lands_iff`). -/

section Lands

variable {Γ : Ctx}

/-- The global part one element leaves, its right-hand sides read in `σ₀`
(`UpdElem.write`'s global part; a local's right-hand side is read for its
halt). -/
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

theorem Held.OKT_iff {Δ : Ctx} (σ₀ : State C Γ) (σ' : State C Δ) {t : LTy} (i : Idx Δ t) :
    (x : Held C Γ t) → (Held.OKT σ₀ σ' i x ↔ Held.OK σ₀.erase σ'.erase i x)
  | .pos j => by
    show σ'.getE i = σ₀.getE j ↔ Env.get i σ'.erase.env = Env.get j σ₀.erase.env
    rw [State.getE_eq, State.getE_eq]
  | .rhs r => by
    show r.evalT σ₀ = .ok (σ'.getE i) ↔ r.eval σ₀.erase = .ok (Env.get i σ'.erase.env)
    rw [State.getE_eq, Rhs.evalT_eq]

/-- What a local holds is fixed by what `U` left in it. -/
theorem Held.OK.unique {Δ : Ctx} {σ₀ : EState C Γ} {σ₁ σ₂ : EState C Δ} {t : LTy}
    {i : Idx Δ t} : (x : Held C Γ t) → Held.OK σ₀ σ₁ i x → Held.OK σ₀ σ₂ i x →
    Env.get i σ₁.env = Env.get i σ₂.env
  | .pos _, h₁, h₂ => h₁.trans h₂.symm
  | .rhs _, h₁, h₂ => Except.ok.inj (h₁.symm.trans h₂)

theorem EState.ext_glob {Δ : Ctx} {σ τ : EState C Δ} (hg : σ.glob = τ.glob) (he : σ.env = τ.env) :
    σ = τ := by
  cases σ; cases τ
  simp only [EState.glob, Semantics.State.mk.injEq] at hg
  obtain ⟨rfl, rfl, rfl, -, rfl, rfl, rfl⟩ := hg
  cases he; rfl

private theorem map_bind_eq {ε α β γ : Type} (f : β → γ) (x : Except ε α)
    (g : α → Except ε β) : Except.map f (x >>= g) = x >>= fun a => Except.map f (g a) := by
  cases x <;> rfl

private theorem map_ite_eq {ε β γ : Type} (f : β → γ) (c : Prop) [Decidable c]
    (a b : Except ε β) :
    Except.map f (if c then a else b) = if c then Except.map f a else Except.map f b := by
  split <;> rfl

theorem UpdElem.write_glob {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElem C Γ Δ) (τ : EState C Δ) :
    (e.write σ₀.erase τ).map EState.glob = e.globT σ₀ τ.glob := by
  cases e <;>
    simp only [UpdElem.write, UpdElem.globT, Rhs.evalT_eq, Tm.evalT_eq, map_bind_eq, map_ite_eq] <;>
    rfl

/-- An update's global part is that of what it computes on the erasure. -/
theorem Upd.apply_glob (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    (U.apply σ₀.erase).map EState.glob = U.globT σ₀
  | _, .nil => rfl
  | _, .snoc U e => by
    rw [Upd.globT, ← Upd.apply_glob σ₀ U]
    show (do e.write σ₀.erase (← U.apply σ₀.erase)).map EState.glob = _
    cases U.apply σ₀.erase with
    | error _ => rfl
    | ok τ => exact UpdElem.write_glob σ₀ e τ
  | _, .decl U _ r => by
    rw [Upd.globT, ← Upd.apply_glob σ₀ U, Rhs.evalT_eq]
    show (do let τ ← U.apply σ₀.erase; pure (τ.push (← r.eval σ₀.erase))).map EState.glob = _
    cases U.apply σ₀.erase <;> cases r.eval σ₀.erase <;> rfl
  | _, .pop U h => by
    rw [Upd.globT, ← Upd.apply_glob σ₀ U]
    show ((U.apply σ₀.erase).map (EState.drop h)).map EState.glob = _
    cases U.apply σ₀.erase <;> rfl
  | _, .drop U h => by
    rw [Upd.globT, ← Upd.apply_glob σ₀ U]
    show ((U.apply σ₀.erase).map (EState.thin h)).map EState.glob = _
    cases U.apply σ₀.erase <;> rfl

/-- **Landing is applying on the erasure.** -/
theorem Upd.lands_iff {Δ : Ctx} {σ₀ : State C Γ} {U : Upd C Γ Δ} {g : Semantics.State}
    {σ' : State C Δ} : U.Lands σ₀ g σ' ↔ U.apply σ₀.erase = .ok σ'.erase ∧ σ'.globE = g := by
  constructor
  · rintro ⟨hg, hσ', hh⟩
    refine ⟨?_, hσ'⟩
    have hm := Upd.apply_glob σ₀ U
    rw [hg] at hm
    cases hτ : U.apply σ₀.erase with
    | error _ => rw [hτ] at hm; cases hm
    | ok τ =>
      rw [hτ] at hm
      have hτg : τ.glob = g := by cases hm; rfl
      refine congrArg Except.ok (EState.ext_glob (hτg.trans hσ'.symm) ?_)
      exact Env.ext_get _ _ fun i => Held.OK.unique _ (Upd.held_ok U hτ i)
        ((Held.OKT_iff σ₀ σ' i _).1 (hh i))
  · rintro ⟨ha, hσ'⟩
    refine ⟨?_, hσ', fun i => (Held.OKT_iff σ₀ σ' i _).2 (Upd.held_ok U ha i)⟩
    rw [← Upd.apply_glob σ₀ U, ha, ← hσ']
    rfl

/-- **`afterT` is the erased reading**: what an update applied to the
erasure leaves, read in every typed state that erases to it. -/
theorem Upd.afterT_iff {Δ : Ctx} (m : Modality) (σ₀ : State C Γ) (U : Upd C Γ Δ)
    (p : State C Δ → Prop) :
    U.afterT m σ₀ p ↔
      m.afterC (fun τ => ∀ σ' : State C Δ, σ'.erase = τ → σ₀.H <+: σ'.H → p σ')
        (U.apply σ₀.erase) := by
  have hm := Upd.apply_glob σ₀ U
  unfold Upd.afterT
  cases hτ : U.apply σ₀.erase with
  | error e =>
    rw [hτ] at hm
    rw [← hm]
    exact Iff.rfl
  | ok τ =>
    rw [hτ] at hm
    rw [← hm]
    show (∀ σ' : State C Δ, U.Lands σ₀ τ.glob σ' → _) ↔ (∀ σ' : State C Δ, σ'.erase = τ → _)
    refine forall_congr' fun σ' => ?_
    have hl : U.Lands σ₀ τ.glob σ' ↔ σ'.erase = τ := by
      rw [Upd.lands_iff, hτ]
      constructor
      · rintro ⟨h, -⟩; cases h; rfl
      · rintro rfl; exact ⟨rfl, rfl⟩
    rw [hl]

/-- What holds after an update holds of a typed state it is known to end
in. -/
theorem Upd.afterT.of_apply {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    {p : State C Δ → Prop} (h : U.afterT m σ₀ p) {σ' : State C Δ}
    (ha : U.apply σ₀.erase = .ok σ'.erase) (hH : σ₀.H <+: σ'.H) : p σ' := by
  rw [Upd.afterT_iff, ha] at h
  exact h σ' rfl hH

end Lands

/-! ## W9.7.2 `close` lane: the typed state's readers, by position

What `sol_close`'s kit (`Calculus/CloseScoped.lean`) and the decision
procedure read a typed state by: its global part (`State.globE`) and its
locals (`State.getE`) after a push, a set, an anonymisation, a havoc, a pop
and a thinning. -/

section CloseKit

variable {Γ : Ctx}

theorem State.globE_push {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) :
    (σ.push v).globE = σ.globE := rfl
theorem State.getE_push_here {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) :
    (σ.push v).getE .here = LTy.TDenote.erase t v := rfl
theorem State.getE_push_there {t u : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) (i : Idx Γ u) :
    (σ.push v).getE (.there i) = σ.getE i := rfl
theorem State.globE_setLocal {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).globE = σ.globE := rfl
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
theorem State.globE_drop {Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) : (σ.drop h).globE = σ.globE :=
  rfl
theorem State.getE_drop {Δ : Ctx} {t : LTy} (h : Ext Γ Δ) (σ : State C Δ) (i : Idx Γ t) :
    (σ.drop h).getE i = σ.getE (i.ext h) := by
  show LTy.TDenote.erase t (TEnv.get i (TEnv.drop h σ.env)) = _
  rw [← TEnv.get_ext_drop]

/-! ### Where an update lands, computed

The global part and the locals an update leaves, as values: `Upd.applyV`
computes the pair a landed state's `State.globE` and `State.getE` read
(`Upd.lands_iff_applyV`), each right-hand side read once in the state the
update is applied in.  The closer reads an update's rest by it
(`CloseS.holds_upd`), and the decision procedure relates its symbols to
it. -/

/-- The locals of `Δ`, erased, by position. -/
abbrev Locs (C : Contract) (Δ : Ctx) : Type := (t : LTy) → Idx Δ t → t.Denote C

/-- A typed state's locals, erased. -/
def State.loc (σ : State C Γ) : Locs C Γ := fun _ i => σ.getE i

/-- A local pushed. -/
def Locs.push {Δ : Ctx} {t : LTy} (ℓ : Locs C Δ) (v : t.Denote C) : Locs C (t :: Δ) :=
  fun _ j => match j with
    | .here => v
    | .there i => ℓ _ i

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

/-- What `U` left in a local, as a value read in `σ₀`. -/
def Held.OKV {t : LTy} (σ₀ : State C Γ) (v : t.Denote C) : Held C Γ t → Prop
  | .pos j => v = σ₀.getE j
  | .rhs r => r.evalT σ₀ = .ok v

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

theorem State.aliasPathT_getE (σ : State C Γ) {R : RefTy} (i : Idx Γ (.alias R)) :
    σ.aliasPathT i = match σ.getE i with
      | some p => .ok p
      | none => .error .revert := by
  unfold State.aliasPathT State.getE
  generalize (TEnv.get i σ.env : Option (SRef C (.ref R))) = x
  cases x <;> rfl

theorem State.memRefT_getE (σ : State C Γ) {R : RefTy} (i : Idx Γ (.mem R)) :
    σ.memRefT i = match σ.getE i with
      | some n => .ok n
      | none => .error .revert := by
  unfold State.memRefT State.getE
  generalize (TEnv.get i σ.env : Option (HRef σ.H R)) = x
  cases x <;> rfl

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
theorem State.globE_thin {Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) : (σ.thin h).globE = σ.globE :=
  rfl
theorem State.loc_thin {Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) : (σ.thin h).loc = σ.loc.thin h := by
  funext u j
  show LTy.TDenote.erase u (TEnv.get j (TEnv.thin h σ.env)) = _
  rw [TEnv.get_thin_wk]
  rfl

open Semantics (bind_ok_inv) in
/-- **The term bridge, typed** (`Tm.denote_eval`): a term's denotation
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
