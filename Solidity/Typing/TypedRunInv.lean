import Solidity.Typing.Soundness
import Solidity.Semantics.StepErase
import Solidity.Semantics.RunWk
import Solidity.Typing.TypedWT

/-!
# Invariants of the typed run, on its erasure

`Typing/Soundness.lean`'s `RunInv` (a part on the erased global state, a
part on each erased local) carried along the typed run
(`Semantics/Run.lean`): `RunInv.TKeeps t` says the step `t`, from a typed
state whose erasure the invariant holds of, ends, if in a state, in one
whose erasure it holds of, each under the store typing its own heap typing
lists (`HTy.toHeapTy 0 σ.H`, decision 75).  The scopes (a branch, a block, a
loop's iteration, a call's frame, a `try`'s clause) only push and pop
locals, so they keep any such invariant once their sub-programs do
(`tkeeps_ite` … `tkeeps_tryCall`, a loop by `TLoop.run_induct`); a statement
without sub-programs keeps it when what it erases to does
(`TKeeps.of_agrees`, through `Semantics/StepErase.lean`), from the erasure
of a typed state, which is well-typed by construction (`State.erase_wt`,
`Typing/TypedWT.lean`): each invariant's own lemma
(`Typing/Reachability.lean`'s canonical storage,
`Typing/Constructibility.lean`'s tight one) needs only what the types do
not already say.
-/

namespace Solidity

open Semantics (Value Res HeapTy bind_ok_inv)

variable {C : Contract}

/-- A typed step that ends in a state: what it erases to ends in that state's
erasure. -/
theorem StepAgrees.ok {Γ Γ' : Ctx} {t : TStep C Γ Γ'} {u : EState C Γ → Res (EState C Γ')}
    (ha : StepAgrees t u) {σ : State C Γ} {o : Out C σ.H Γ'} (h : t σ = .ok o) :
    u σ.erase = .ok o.st.erase := by
  have hu := ha σ
  rw [h] at hu
  exact hu

/-- A heap typing that grew lists a store typing that only grew. -/
theorem HTy.toHeapTy_extends {H H' : HTy} (h : H <+: H') :
    (HTy.toHeapTy 0 H).Extends (HTy.toHeapTy 0 H') := by
  intro id ty hid
  have h₁ := HTy.lookupBy_toHeapTy (start := 0) H id
  have h₂ := HTy.lookupBy_toHeapTy (start := 0) H' id
  rw [Nat.zero_add] at h₁ h₂
  rw [h₁] at hid
  rw [h₂]
  obtain ⟨t, rfl⟩ := h
  cases hi : H[id]? with
  | none => rw [hi] at hid; cases hid
  | some R =>
    rw [hi] at hid
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1, hi]
    exact hid

namespace RunInv

variable {I : RunInv C}

/-- A typed step keeps the invariant on the erasure: from a typed state
whose erasure it holds of, under the store typing its heap typing lists, the
step ends, if in a state, in one whose erasure it holds of under its own. -/
def TKeeps {Γ Γ' : Ctx} (I : RunInv C) (t : TStep C Γ Γ') : Prop :=
  ∀ (σ : State C Γ) (o : Out C σ.H Γ'), I.Holds (HTy.toHeapTy 0 σ.H) σ.erase → t σ = .ok o →
    I.Holds (HTy.toHeapTy 0 o.st.H) o.st.erase

/-- What a leaf proves on its erasure `u`: from a typed state whose erasure
the invariant holds of (and which is well-typed by construction,
`State.erase_wt`), what `u` ends in, if it is the erasure of a typed state
over a grown heap typing, holds the invariant under that state's store
typing. -/
def EKeeps {Γ Γ' : Ctx} (I : RunInv C) (u : EState C Γ → Res (EState C Γ')) : Prop :=
  ∀ (σ : State C Γ) (σ' : EState C Γ'), RunWT C (HTy.toHeapTy 0 σ.H) σ.erase →
    I.Holds (HTy.toHeapTy 0 σ.H) σ.erase → u σ.erase = .ok σ' →
    ∀ (τ : State C Γ'), σ.H <+: τ.H → τ.erase = σ' → I.Holds (HTy.toHeapTy 0 τ.H) σ'

/-- **A leaf, through its erasure**: a typed step keeps the invariant when
what it erases to does (`Semantics/StepErase.lean`). -/
theorem TKeeps.of_agrees (hnd : Semantics.nodupKeysB C.vars = true) {Γ Γ' : Ctx} {t : TStep C Γ Γ'}
    {u : EState C Γ → Res (EState C Γ')} (ha : StepAgrees t u) (hk : I.EKeeps u) : I.TKeeps t :=
  fun σ o hσ h => hk σ o.st.erase (State.erase_wt hnd σ) hσ (ha.ok h) o.st o.ext rfl

theorem TKeeps.drop {Γ Δ Δ' : Ctx} {t : TStep C Γ Δ} (hf : I.TKeeps t) (x : Ext Δ' Δ) :
    I.TKeeps (fun σ => (t σ).map fun o => ⟨o.st.drop x, o.ext⟩) := by
  intro σ o hσ h
  dsimp only at h
  cases hr : t σ with
  | error e => rw [hr] at h; cases h
  | ok o₁ =>
    rw [hr] at h
    cases h
    show I.Holds (HTy.toHeapTy 0 o₁.st.H) (o₁.st.drop x).erase
    rw [State.drop_erase]
    exact (hf σ o₁ hσ hr).drop x

theorem tkeeps_seq {Γ Γ₁ Γ₂ : Ctx} {s : TStep C Γ Γ₁} {P : TStep C Γ₁ Γ₂} (hs : I.TKeeps s)
    (hP : I.TKeeps P) : I.TKeeps (TRun.seq s P) := by
  intro σ o hσ h
  unfold TRun.seq at h
  split at h
  · rename_i o₁ ho₁
    cases hp : P o₁.st with
    | error => rw [hp] at h; cases h
    | ok o₂ =>
      rw [hp] at h
      cases h
      exact hP o₁.st o₂ (hs σ o₁ hσ ho₁) hp
  · cases h

theorem tkeeps_nil {Γ : Ctx} : I.TKeeps (TRun.nil : TStep C Γ Γ) := by
  intro σ o hσ h
  cases h
  exact hσ

theorem tkeeps_ite {Γ Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁) {thn : TStep C Γ Γ₁}
    (h₂ : Ext Γ Γ₂) {els : TStep C Γ Γ₂} (hthn : I.TKeeps thn) (hels : I.TKeeps els) :
    I.TKeeps (TRun.ite c h₁ thn h₂ els) := by
  intro σ o hσ h
  unfold TRun.ite at h
  cases hv : c.evalT σ with
  | error => rw [hv] at h; cases h
  | ok v =>
    rw [hv, ok_bind] at h
    split at h
    · exact hthn.drop h₁ σ o hσ h
    · exact hels.drop h₂ σ o hσ h

theorem tkeeps_block {Γ Γ₁ : Ctx} (x : Ext Γ Γ₁) {body : TStep C Γ Γ₁} (hb : I.TKeeps body) :
    I.TKeeps (TRun.block x body) :=
  hb.drop x

theorem tkeeps_require {Γ : Ctx} (c : Val C Γ .bool) : I.TKeeps (TRun.require c) := by
  intro σ o hσ h
  unfold TRun.require at h
  cases hv : c.evalT σ with
  | error => rw [hv] at h; cases h
  | ok v =>
    rw [hv, ok_bind] at h
    split at h
    · cases h; exact hσ
    · cases h

theorem tkeeps_assert {Γ : Ctx} (c : Val C Γ .bool) : I.TKeeps (TRun.assert c) := by
  intro σ o hσ h
  unfold TRun.assert at h
  cases hv : c.evalT σ with
  | error => rw [hv] at h; cases h
  | ok v =>
    rw [hv, ok_bind] at h
    split at h
    · cases h; exact hσ
    · cases h

theorem tkeeps_revert {Γ : Ctx} :
    I.TKeeps (fun _ : State C Γ => (.error .revert : TRes (Out C _ Γ))) :=
  fun _ _ _ h => nomatch h

theorem tkeeps_loop {Γ Γ₁ : Ctx} (c : Val C Γ .bool) (x : Ext Γ Γ₁) {body : TStep C Γ Γ₁}
    (hb : I.TKeeps body) : I.TKeeps (TRun.loop c x body) := by
  intro σ o hσ h
  unfold TRun.loop at h
  refine TLoop.run_induct (P := fun o : Out C σ.H Γ => I.Holds (HTy.toHeapTy 0 o.st.H) o.st.erase)
    (Q := fun r => ∀ o, r = .ok o → I.Holds (HTy.toHeapTy 0 o.st.H) o.st.erase)
    hσ (fun τ h₁ => ?_) (fun _ h => nomatch h) _ h
  simp only [TLoop.step]
  rcases c.evalT τ.st with _ | b
  · exact fun _ h => nomatch h
  · cases b
    · exact fun _ h => by cases h; exact h₁
    · dsimp only
      cases hr : body τ.st with
      | error => exact fun _ h => nomatch h
      | ok τ' =>
        show I.Holds (HTy.toHeapTy 0 τ'.st.H) (τ'.st.drop x).erase
        rw [State.drop_erase]
        exact (hb τ.st τ' h₁ hr).drop x

/-- A call keeps the invariant when its arguments, its entry (the frame's
return variables, a memory one allocated) and its body do. -/
theorem tkeeps_call {Γ Γ' ps rs Γf : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (x : Ext (rs ++ ps) Γf) {body : TStep C (rs ++ ps) Γf}
    (hargs : ∀ (H : HeapTy) (σ : EState C Γ) (a : Env C ps), I.Holds H σ → args.eval σ = .ok a →
      Env.All (I.loc H) a)
    (henter : ∀ (σ : State C Γ) (a : TEnv C σ.H ps),
      I.Holds (HTy.toHeapTy 0 σ.H) (σ.withEnv a).erase →
      I.Holds (HTy.toHeapTy 0 (ret.enterT (σ.withEnv a)).st.H) (ret.enterT (σ.withEnv a)).st.erase)
    (hb : I.TKeeps body) : I.TKeeps (TRun.call args ret x body) := by
  intro σ o hσ h
  unfold TRun.call at h
  cases ha : args.evalT σ with
  | error => rw [ha] at h; cases h
  | ok a =>
    rw [ha, ok_bind] at h
    dsimp only at h
    have hae := Args.evalT_erase σ args
    rw [ha] at hae
    have h₁ := henter σ a (by
      rw [State.withEnv_erase]
      exact hσ.withEnv (hargs _ σ.erase _ hσ hae))
    cases hr : body (ret.enterT (σ.withEnv a)).st with
    | error => rw [hr] at h; cases h
    | ok o₂ =>
      rw [hr, ok_bind] at h
      cases h
      have h₂ := hb _ o₂ h₁ hr
      rw [State.withEnv_erase]
      refine h₂.withEnv ?_
      rw [CallRet.leaveT_erase, TEnv.erase_wk, ← TEnv.take_erase, ← TEnv.drop_erase]
      exact CallRet.leave_all ret
        (env_mono (HTy.toHeapTy_extends ((ret.enterT (σ.withEnv a)).ext.trans o₂.ext)) hσ.2)
        (Env.All.take rs (Env.All.drop x h₂.2))

/-- A call's entry, read on the erasure: `CallRet.enter` on the caller's
global state, the frame's return variables before the arguments. -/
theorem _root_.Solidity.CallRet.enterT_ok {Γ Γ' ps rs : Ctx} (ret : CallRet Γ rs Γ')
    (σ : State C Γ) (a : TEnv C σ.H ps) :
    ∃ τ' r, ret.enter σ.erase.glob = .ok (τ', r) ∧
      (ret.enterT (σ.withEnv a)).st.erase =
        EState.ofGlob τ' (Env.append rs r (TEnv.erase ps a)) := by
  have he := CallRet.enterT_erase ret σ a (fun s => (pure s : Res _))
  obtain ⟨⟨τ', r⟩, hen, he⟩ := bind_ok_inv he
  exact ⟨τ', r, hen, (Except.ok.inj he).symm⟩

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
  intro σ o hσ h
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
      refine hok.drop ((Ext.append Γ ρ).trans h₁) (σ.withEnv (TEnv.append ρ r σ.env)) o ?_ h
      show I.Holds (HTy.toHeapTy 0 σ.H) _
      rw [State.withEnv_erase, TEnv.append_erase]
      have hd := Binders.decodeT_erase (C := C) (H := σ.H) rets vs
      rw [hr] at hd
      exact hσ.withEnv (Env.All.append ρ (hdec _ vs _ rest hd) hσ.2)
  · exact herr.drop h₂ σ o hσ h
  · rename_i c _
    cases hr : code.decodeT (H := σ.H) c with
    | error => rw [hr] at h; cases h
    | ok r =>
      rw [hr, ok_bind] at h
      refine hpnc.drop ((Ext.append Γ κ).trans h₃) (σ.withEnv (TEnv.append κ r σ.env)) o ?_ h
      show I.Holds (HTy.toHeapTy 0 σ.H) _
      rw [State.withEnv_erase, TEnv.append_erase]
      have hd := CodeBinder.decodeT_erase (C := C) (H := σ.H) code c
      rw [hr] at hd
      exact hσ.withEnv (Env.All.append κ (hcode _ c _ hd) hσ.2)
  · exact hoth.drop h₄ σ o hσ h

end RunInv

end Solidity
