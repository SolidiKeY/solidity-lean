import Solidity.Calculus.Step
import Solidity.Semantics.Erased
import Solidity.Update
import Solidity.Theory.Observe
import Solidity.Typing.Soundness
import Solidity.Semantics.RunFrame

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

/-! ## The typed kit

What the update laws read `afterT` by (W9.7.2), with no erasure: two
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

/-- Two typed states of one erasure read alike. -/
theorem State.ReadsAs.of_erase {σ σ' : State C Γ} (he : σ.erase = σ'.erase) : σ.ReadsAs σ' :=
  ⟨by rw [State.globE_eq, State.globE_eq, he], fun i => by rw [State.getE_eq, State.getE_eq, he]⟩

/-- Two typed states that read alike have one erasure. -/
theorem State.ReadsAs.erase_eq {σ σ' : State C Γ} (h : σ.ReadsAs σ') : σ.erase = σ'.erase := by
  have hg : σ.erase.glob = σ'.erase.glob := by rw [← State.globE_eq, ← State.globE_eq, h.1]
  refine EState.ext_glob hg (Env.ext_get _ _ fun i => ?_)
  rw [← State.getE_eq, ← State.getE_eq, h.2 i]

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

end Kit

end Solidity
