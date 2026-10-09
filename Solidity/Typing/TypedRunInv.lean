import Solidity.Typing.Soundness
import Solidity.Semantics.Core.TypedStepErase
import Solidity.Semantics.Core.TypedRunWk

/-!
# Invariants of the typed run, on its erasure

`Typing/Soundness.lean`'s `RunInv` (a part on the erased global state, a
part on each erased local) carried along the typed run
(`Semantics/Core/TypedRun.lean`): `RunInv.TKeeps t` says the step `t`, from
a typed state whose erasure the invariant holds of, ends, if in a state, in
one whose erasure it holds of, under a store typing that only grew.  The
scopes (a branch, a block, a loop's iteration, a call's frame, a `try`'s
clause) only push and pop locals, so they keep any such invariant once their
sub-programs do (`tkeeps_ite` … `tkeeps_tryCall`, a loop by
`TLoop.run_induct`); a statement without sub-programs keeps it when what it erases to does
(`TKeeps.of_agrees`, through `Semantics/Core/TypedStepErase.lean`), which is
each invariant's own lemma (`Typing/Reachability.lean`'s canonical
storage, `Typing/Constructibility.lean`'s tight one).  The typed state is
well-typed by construction (`Typing/TypedWT.lean`), so type soundness itself
needs no such proof.
-/

namespace Solidity.Core

open Semantics (Value Res HeapTy bind_ok_inv)

variable {C : Contract}

/-- A typed step that ends in a state: what it erases to ends in that state's
erasure. -/
theorem StepAgrees.ok {Γ Γ' : Ctx} {t : TStep C Γ Γ'} {u : EState C Γ → Res (EState C Γ')}
    (ha : StepAgrees t u) {σ : TState C Γ} {o : Out C σ.H Γ'} (h : t σ = .ok o) :
    u σ.erase = .ok o.st.erase := by
  have hu := ha σ
  rw [h] at hu
  exact hu

namespace RunInv

variable {I : RunInv C}

/-- A typed step keeps the invariant on the erasure: from a state whose
erasure it holds of, the step ends, if in a state, in one whose erasure it
holds of under a store typing that only grew. -/
def TKeeps {Γ Γ' : Ctx} (I : RunInv C) (t : TStep C Γ Γ') : Prop :=
  ∀ (H : HeapTy) (σ : TState C Γ) (o : Out C σ.H Γ'), I.Holds H σ.erase → t σ = .ok o →
    ∃ H', H.Extends H' ∧ I.Holds H' o.st.erase

/-- **A leaf, through its erasure**: a typed step keeps the invariant when
what it erases to does (`Semantics/Core/TypedStepErase.lean`). -/
theorem TKeeps.of_agrees {Γ Γ' : Ctx} {t : TStep C Γ Γ'} {u : EState C Γ → Res (EState C Γ')}
    (ha : StepAgrees t u) (hk : I.Keeps u) : I.TKeeps t := by
  intro H σ o hσ h
  exact hk H σ.erase o.st.erase hσ (ha.ok h)

theorem TKeeps.drop {Γ Δ Δ' : Ctx} {t : TStep C Γ Δ} (hf : I.TKeeps t) (x : Ext Δ' Δ) :
    I.TKeeps (fun σ => (t σ).map fun o => ⟨o.st.drop x, o.ext⟩) := by
  intro H σ o hσ h
  dsimp only at h
  cases hr : t σ with
  | error e => rw [hr] at h; cases h
  | ok o₁ =>
    rw [hr] at h
    cases h
    obtain ⟨H', hext, h'⟩ := hf H σ o₁ hσ hr
    refine ⟨H', hext, ?_⟩
    show I.Holds H' (o₁.st.drop x).erase
    rw [TState.drop_erase]
    exact h'.drop x

theorem tkeeps_seq {Γ Γ₁ Γ₂ : Ctx} {s : TStep C Γ Γ₁} {P : TStep C Γ₁ Γ₂} (hs : I.TKeeps s)
    (hP : I.TKeeps P) : I.TKeeps (TRun.seq s P) := by
  intro H σ o hσ h
  unfold TRun.seq at h
  split at h
  · rename_i o₁ ho₁
    obtain ⟨H₁, hext₁, h₁⟩ := hs H σ o₁ hσ ho₁
    cases hp : P o₁.st with
    | error => rw [hp] at h; cases h
    | ok o₂ =>
      rw [hp] at h
      cases h
      obtain ⟨H₂, hext₂, h₂⟩ := hP H₁ o₁.st o₂ h₁ hp
      exact ⟨H₂, hext₁.trans hext₂, h₂⟩
  · cases h

theorem tkeeps_nil {Γ : Ctx} : I.TKeeps (TRun.nil : TStep C Γ Γ) := by
  intro H σ o hσ h
  cases h
  exact ⟨H, .refl H, hσ⟩

theorem tkeeps_ite {Γ Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁) {thn : TStep C Γ Γ₁}
    (h₂ : Ext Γ Γ₂) {els : TStep C Γ Γ₂} (hthn : I.TKeeps thn) (hels : I.TKeeps els) :
    I.TKeeps (TRun.ite c h₁ thn h₂ els) := by
  intro H σ o hσ h
  unfold TRun.ite at h
  cases hv : c.evalT σ with
  | error => rw [hv] at h; cases h
  | ok v =>
    rw [hv, ok_bind] at h
    split at h
    · exact hthn.drop h₁ H σ o hσ h
    · exact hels.drop h₂ H σ o hσ h

theorem tkeeps_block {Γ Γ₁ : Ctx} (x : Ext Γ Γ₁) {body : TStep C Γ Γ₁} (hb : I.TKeeps body) :
    I.TKeeps (TRun.block x body) :=
  hb.drop x

theorem tkeeps_require {Γ : Ctx} (c : Val C Γ .bool) : I.TKeeps (TRun.require c) := by
  intro H σ o hσ h
  unfold TRun.require at h
  cases hv : c.evalT σ with
  | error => rw [hv] at h; cases h
  | ok v =>
    rw [hv, ok_bind] at h
    split at h
    · cases h; exact ⟨H, .refl H, hσ⟩
    · cases h

theorem tkeeps_assert {Γ : Ctx} (c : Val C Γ .bool) : I.TKeeps (TRun.assert c) := by
  intro H σ o hσ h
  unfold TRun.assert at h
  cases hv : c.evalT σ with
  | error => rw [hv] at h; cases h
  | ok v =>
    rw [hv, ok_bind] at h
    split at h
    · cases h; exact ⟨H, .refl H, hσ⟩
    · cases h

theorem tkeeps_revert {Γ : Ctx} :
    I.TKeeps (fun _ : TState C Γ => (.error .revert : TRes (Out C _ Γ))) :=
  fun _ _ _ _ h => nomatch h

theorem tkeeps_loop {Γ Γ₁ : Ctx} (c : Val C Γ .bool) (x : Ext Γ Γ₁) {body : TStep C Γ Γ₁}
    (hb : I.TKeeps body) : I.TKeeps (TRun.loop c x body) := by
  intro H σ o hσ h
  unfold TRun.loop at h
  refine TLoop.run_induct (P := fun o : Out C σ.H Γ => ∃ H', H.Extends H' ∧ I.Holds H' o.st.erase)
    (Q := fun r => ∀ o, r = .ok o → ∃ H', H.Extends H' ∧ I.Holds H' o.st.erase)
    ⟨H, .refl H, hσ⟩ (fun τ ⟨H₁, hext₁, h₁⟩ => ?_) (fun _ h => nomatch h) _ h
  simp only [TLoop.step]
  rcases c.evalT τ.st with _ | b
  · exact fun _ h => nomatch h
  · cases b
    · exact fun _ h => by cases h; exact ⟨H₁, hext₁, h₁⟩
    · dsimp only
      cases hr : body τ.st with
      | error => exact fun _ h => nomatch h
      | ok τ' =>
        obtain ⟨H₂, hext₂, h₂⟩ := hb H₁ τ.st τ' h₁ hr
        refine ⟨H₂, hext₁.trans hext₂, ?_⟩
        show I.Holds H₂ (τ'.st.drop x).erase
        rw [TState.drop_erase]
        exact h₂.drop x

theorem tkeeps_call {Γ Γ' ps rs Γf : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (x : Ext (rs ++ ps) Γf) {body : TStep C (rs ++ ps) Γf}
    (hargs : ∀ (H : HeapTy) (σ : EState C Γ) (a : Env C ps), I.Holds H σ → args.eval σ = .ok a →
      Env.All (I.loc H) a)
    (henter : ∀ (H : HeapTy) (τ τ' : Semantics.State) (r : Env C rs), I.glob H τ →
      ret.enter τ = .ok (τ', r) → ∃ H', H.Extends H' ∧ I.glob H' τ' ∧ Env.All (I.loc H') r)
    (hb : I.TKeeps body) : I.TKeeps (TRun.call args ret x body) := by
  intro H σ o hσ h
  unfold TRun.call at h
  cases ha : args.evalT σ with
  | error => rw [ha] at h; cases h
  | ok a =>
    rw [ha, ok_bind] at h
    dsimp only at h
    have hae := Args.evalT_erase σ args
    rw [ha] at hae
    have hA := hargs H σ.erase _ hσ hae
    have he := CallRet.enterT_erase ret σ a (fun s => (pure s : Res _))
    obtain ⟨⟨τ', r⟩, hen, he⟩ := bind_ok_inv he
    obtain ⟨H₁, hext₁, hg₁, hr₁⟩ := henter H σ.erase.glob τ' r hσ.1 hen
    have h₁ : I.Holds H₁ (ret.enterT (σ.withEnv a)).st.erase := by
      rw [← Except.ok.inj he]
      exact ⟨I.reglob _ hg₁, Env.All.append rs hr₁ (env_mono hext₁ hA)⟩
    cases hr : body (ret.enterT (σ.withEnv a)).st with
    | error => rw [hr] at h; cases h
    | ok o₂ =>
      rw [hr, ok_bind] at h
      cases h
      obtain ⟨H₂, hext₂, h₂⟩ := hb H₁ _ o₂ h₁ hr
      refine ⟨H₂, hext₁.trans hext₂, ?_⟩
      rw [TState.withEnv_erase]
      refine h₂.withEnv ?_
      rw [CallRet.leaveT_erase, TEnv.erase_wk, ← TEnv.take_erase, ← TEnv.drop_erase]
      exact CallRet.leave_all ret (env_mono (hext₁.trans hext₂) hσ.2)
        (Env.All.take rs (Env.All.drop x h₂.2))

theorem tkeeps_tryCall {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) {ok : TStep C (ρ ++ Γ) Γ₁}
    (h₂ : Ext Γ Γ₂) {err : TStep C Γ Γ₂} (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) {pnc : TStep C (κ ++ Γ) Γ₃}
    (h₄ : Ext Γ Γ₄) {other : TStep C Γ Γ₄}
    (hdec : ∀ (H : HeapTy) (vs : List Value) (r : Env C ρ) (rest : List Value),
      rets.decode vs = .ok (r, rest) → Env.All (I.loc H) r)
    (hcode : ∀ (H : HeapTy) (c : Value) (r : Env C κ), code.decode c = .ok r → Env.All (I.loc H) r)
    (hok : I.TKeeps ok) (herr : I.TKeeps err) (hpnc : I.TKeeps pnc) (hoth : I.TKeeps other) :
    I.TKeeps (TRun.tryCall call rets h₁ ok h₂ err code h₃ pnc h₄ other) := by
  intro H σ o hσ h
  unfold TRun.tryCall at h
  split at h
  · cases h
  · rename_i vs _
    cases hr : Binders.decodeT (H := σ.H) rets vs with
    | error => rw [hr] at h; cases h
    | ok x =>
      obtain ⟨r, rest⟩ := x
      rw [hr, ok_bind] at h
      dsimp only at h
      refine hok.drop ((Ext.append Γ ρ).trans h₁) H (σ.withEnv (TEnv.append ρ r σ.env)) o ?_ h
      rw [TState.withEnv_erase, TEnv.append_erase]
      have hd := Binders.decodeT_erase (C := C) (H := σ.H) rets vs
      rw [hr] at hd
      exact hσ.withEnv (Env.All.append ρ (hdec H vs _ rest hd) hσ.2)
  · exact herr.drop h₂ H σ o hσ h
  · rename_i c _
    cases hr : code.decodeT (H := σ.H) c with
    | error => rw [hr] at h; cases h
    | ok r =>
      rw [hr, ok_bind] at h
      refine hpnc.drop ((Ext.append Γ κ).trans h₃) H (σ.withEnv (TEnv.append κ r σ.env)) o ?_ h
      rw [TState.withEnv_erase, TEnv.append_erase]
      have hd := CodeBinder.decodeT_erase (C := C) (H := σ.H) code c
      rw [hr] at hd
      exact hσ.withEnv (Env.All.append κ (hcode H c _ hd) hσ.2)
  · exact hoth.drop h₄ H σ o hσ h

end RunInv

end Solidity.Core
