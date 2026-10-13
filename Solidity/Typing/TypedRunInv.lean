import Solidity.Typing.Soundness
import Solidity.Semantics.RunFrame
import Solidity.Typing.TypedWT

/-!
# Invariants of the typed run

`Typing/Soundness.lean`'s `RunInv` (a part on the untyped global state, a
part on each erased local) read of a typed state (`RunInv.HoldsT`: its
global part erased, `State.globE`, its locals erased, `TEnv.All`) and carried along the typed
run (`Semantics/Run.lean`): `RunInv.TKeeps t` says the step `t`, from a typed
state the invariant holds of, ends, if in a state, in one it holds of, each
under the store typing its own heap typing lists (`HTy.toHeapTy 0 σ.H`,
decision 75).  The scopes (a branch, a block, a loop's iteration, a call's
frame, a `try`'s clause) only push and pop locals, so they keep any such
invariant once their sub-programs do (`tkeeps_ite` … `tkeeps_tryCall`, a
loop by `TLoop.run_induct`); a call's arguments, return variables and
decoded data are values or fresh memory objects, which every invariant
here accepts (`RunInv.ValMemOk`).  A statement without sub-programs is each
invariant's own lemma, read on `TRun.*` through the storage and heap
erasure lemmas (`Semantics/StorageErase.lean`, `Semantics/HeapErase.lean`):
`Typing/Reachability.lean`'s canonical storage,
`Typing/Constructibility.lean`'s tight one, `Typing/Fits.lean`'s bounds.
A typed state is well-typed by construction (`State.glob_wt`,
`Typing/TypedWT.lean`), so an invariant needs only what the types do not
already say.
-/

namespace Solidity

open Semantics (Value Res HeapTy)

variable {C : Contract}

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

theorem TRes.ofOpt_ok {α : Type} {x : Option α} {a : α} (h : TRes.ofOpt x = .ok a) :
    x = some a := by
  cases x with
  | none => exact nomatch h
  | some b => cases h; rfl

/-- `b.f`, erased: the member's segment appended. -/
theorem SRef.field_erase {s f : Name} {T : Ty} (r : SRef C (.ref (.struct s)))
    (h : C.fieldType s f = some T) :
    (r.field h).erase = (r.root, r.path.erase ++ [.field f]) := by
  simp only [SRef.field, SRef.erase, SRef.append, Path.erase_append]
  rfl

/-- `b[i]`, erased: the index's segment appended. -/
theorem SRef.index_erase {R : RefTy} {k : PrimTy} {V : Ty} (r : SRef C (.ref R))
    (it : IndexTy R k V) (i : Int) : (r.index it i).erase = (r.root, r.path.erase ++ [.at i]) := by
  simp only [SRef.index, SRef.erase, SRef.append, Path.erase_append, Path.erase_index]

/-! ## Typed locals that satisfy a predicate -/

/-- Locals of value and memory types only. -/
def Ctx.ValMem : Ctx → Prop
  | [] => True
  | .val _ :: Γ => Ctx.ValMem Γ
  | .mem _ :: Γ => Ctx.ValMem Γ
  | _ :: _ => False

/-- Every local of `e`, erased, satisfies `P` at its type. -/
def TEnv.All {H : HTy} (P : (t : LTy) → t.Denote C → Prop) : {Γ : Ctx} → TEnv C H Γ → Prop
  | [], _ => True
  | t :: _, e => P t (LTy.TDenote.erase t e.1) ∧ TEnv.All P e.2

theorem TEnv.All.mono {H : HTy} {P Q : (t : LTy) → t.Denote C → Prop}
    (hPQ : ∀ t v, P t v → Q t v) : {Γ : Ctx} → {e : TEnv C H Γ} → TEnv.All P e → TEnv.All Q e
  | [], _, _ => trivial
  | _ :: _, _, he => ⟨hPQ _ _ he.1, mono hPQ he.2⟩

theorem TEnv.All.get {H : HTy} {P : (t : LTy) → t.Denote C → Prop} {Γ : Ctx} {t : LTy}
    (i : Idx Γ t) : {e : TEnv C H Γ} → TEnv.All P e → P t (LTy.TDenote.erase t (TEnv.get i e)) := by
  induction i with
  | here => intro e h; exact h.1
  | there i ih => intro e h; exact ih h.2

namespace RunInv

variable {I : RunInv C}

theorem env_mono {Γ : Ctx} {H H' : HeapTy} {K : HTy} (hext : H.Extends H') {e : TEnv C K Γ}
    (h : TEnv.All (I.loc H) e) : TEnv.All (I.loc H') e :=
  TEnv.All.mono (fun _ _ => I.loc_mono hext) h

end RunInv

namespace TEnv.All

variable {P : (t : LTy) → t.Denote C → Prop} {H : HTy}

theorem append {Γ : Ctx} : (ρ : Ctx) → {r : TEnv C H ρ} → {e : TEnv C H Γ} →
    TEnv.All P r → TEnv.All P e → TEnv.All P (TEnv.append ρ r e)
  | [], _, _, _, he => he
  | _ :: ρ, _, _, hr, he => ⟨hr.1, append ρ hr.2 he⟩

theorem take {Γ : Ctx} : (ρ : Ctx) → {e : TEnv C H (ρ ++ Γ)} →
    TEnv.All P e → TEnv.All P (TEnv.take ρ e)
  | [], _, _ => trivial
  | _ :: ρ, _, he => ⟨he.1, take ρ he.2⟩

theorem drop {Γ : Ctx} : {Δ : Ctx} → (h : Ext Γ Δ) → {e : TEnv C H Δ} → TEnv.All P e →
    TEnv.All P (TEnv.drop h e) := by
  intro Δ h
  induction h with
  | refl => intro e he; exact he
  | push h ih => intro e he; exact ih he.2

theorem set : {Γ : Ctx} → {t : LTy} → (i : Idx Γ t) → {e : TEnv C H Γ} → {v : t.TDenote C H} →
    TEnv.All P e → P t (LTy.TDenote.erase t v) → TEnv.All P (TEnv.set i v e) := by
  intro Γ t i
  induction i with
  | here => intro e v h hv; exact ⟨hv, h.2⟩
  | there i ih => intro e v h hv; exact ⟨h.1, ih h.2 hv⟩

theorem wk {H' : HTy} (x : H <+: H') : {Γ : Ctx} → {e : TEnv C H Γ} →
    TEnv.All P e → TEnv.All P (TEnv.wk x Γ e)
  | [], _, _ => trivial
  | t :: _, e, he => ⟨by show P t (LTy.TDenote.erase t (LTy.TDenote.wk x t e.1)); rw [LTy.TDenote.erase_wk]; exact he.1, wk x he.2⟩

/-- A predicate that every value and every memory local satisfies holds of
locals of those types. -/
theorem of_valMem (hv : ∀ p v, P (.val p) v) (hm : ∀ R v, P (.mem R) v) :
    {Γ : Ctx} → Ctx.ValMem Γ → (e : TEnv C H Γ) → TEnv.All P e
  | [], _, _ => trivial
  | .val _ :: Γ, h, e => ⟨hv _ _, of_valMem hv hm (Γ := Γ) h e.2⟩
  | .mem _ :: Γ, h, e => ⟨hm _ _, of_valMem hv hm (Γ := Γ) h e.2⟩
  | .alias _ :: _, h, _ => nomatch h
  | .old :: _, h, _ => nomatch h
  | .oldNet :: _, h, _ => nomatch h
  | .kint :: _, h, _ => nomatch h

end TEnv.All

theorem Args.valMem {Γ : Ctx} : {ps : Ctx} → Args C Γ ps → Ctx.ValMem ps
  | _, .nil => trivial
  | .val _ :: ps, .snoc as _ _ _ => (Args.valMem as : Ctx.ValMem ps)

theorem Binders.valMem : {ρ : Ctx} → Binders ρ → Ctx.ValMem ρ
  | _, .nil => trivial
  | .val _ :: ρ, .snoc bs _ _ => (Binders.valMem bs : Ctx.ValMem ρ)

theorem CodeBinder.valMem {κ : Ctx} (code : CodeBinder κ) : Ctx.ValMem κ := by
  cases code <;> trivial

/-- Leaving a call keeps every local satisfying `P` when the caller's and the
frame's return variables do. -/
theorem CallRet.leaveT_all {P : (t : LTy) → t.Denote C → Prop} {H : HTy} {Γ rs Γ' : Ctx}
    (ret : CallRet Γ rs Γ') {e : TEnv C H Γ} {r : TEnv C H rs}
    (he : TEnv.All P e) (hr : TEnv.All P r) :
    TEnv.All P (ret.leaveT e r) := by
  cases ret with
  | none => exact he
  | val p x res =>
    cases res with
    | none => exact he
    | some i => exact TEnv.All.set i he hr.1
  | rets bs => exact TEnv.All.append _ hr he
  | mem R x hd hm => exact ⟨hr.1, he⟩

/-- Entering a call leaves the storage alone. -/
theorem CallRet.enterT_storage {Γ rs Γ' ps : Ctx} (ret : CallRet Γ rs Γ') (τ : State C ps) :
    (ret.enterT τ).st.storage = τ.storage := by
  cases ret <;> rfl

/-- Entering a call: the frame's return variables, values or a fresh memory
object, on top of the parameters. -/
theorem CallRet.enterT_env {P : (t : LTy) → t.Denote C → Prop} {Γ rs Γ' ps : Ctx}
    (ret : CallRet Γ rs Γ') (τ : State C ps) (hv : ∀ p v, P (.val p) v)
    (hm : ∀ R v, P (.mem R) v) (he : TEnv.All P τ.env) :
    TEnv.All P (ret.enterT τ).st.env := by
  cases ret with
  | none => exact he
  | val p x res => exact ⟨hv _ _, he⟩
  | rets bs =>
    exact TEnv.All.append _ (TEnv.All.of_valMem hv hm (Binders.valMem bs) _) he
  | mem R x hd hm' => exact ⟨hm _ _, TEnv.All.wk _ he⟩

/-! ## Invariants of the typed run -/

namespace RunInv

variable {I : RunInv C}

/-- The invariant holds of a typed state under the store typing `H`: of the
global part erased, and of each local erased. -/
def HoldsT (I : RunInv C) {Γ : Ctx} (H : HeapTy) (σ : State C Γ) : Prop :=
  I.glob H σ.globE ∧ TEnv.All (I.loc H) σ.env

/-- The locals replaced. -/
theorem HoldsT.withEnv {Γ Δ : Ctx} {H : HeapTy} {σ : State C Γ} (h : I.HoldsT H σ)
    {e : TEnv C σ.H Δ} (he : TEnv.All (I.loc H) e) : I.HoldsT H (σ.withEnv e) :=
  ⟨h.1, he⟩

theorem HoldsT.drop {Γ Δ : Ctx} {H : HeapTy} {σ : State C Δ} (h : I.HoldsT H σ) (x : Ext Γ Δ) :
    I.HoldsT H (σ.drop x) :=
  ⟨h.1, TEnv.All.drop x h.2⟩

theorem HoldsT.setLocal {Γ : Ctx} {H : HeapTy} {σ : State C Γ} (h : I.HoldsT H σ) {t : LTy}
    (i : Idx Γ t) {v : t.TDenote C σ.H} (hv : I.loc H t (LTy.TDenote.erase t v)) :
    I.HoldsT H (σ.setLocal i v) :=
  ⟨h.1, TEnv.All.set i h.2 hv⟩

theorem HoldsT.push {Γ : Ctx} {H : HeapTy} {σ : State C Γ} (h : I.HoldsT H σ) {t : LTy}
    {v : t.TDenote C σ.H} (hv : I.loc H t (LTy.TDenote.erase t v)) :
    I.HoldsT H (σ.push v) :=
  ⟨h.1, hv, h.2⟩

/-- A typed step keeps the invariant: from a typed state it holds of, under
the store typing its heap typing lists, the step ends, if in a state, in one
it holds of under its own. -/
def TKeeps {Γ Γ' : Ctx} (I : RunInv C) (t : TStep C Γ Γ') : Prop :=
  ∀ (σ : State C Γ) (o : Out C σ.H Γ'), I.HoldsT (HTy.toHeapTy 0 σ.H) σ → t σ = .ok o →
    I.HoldsT (HTy.toHeapTy 0 o.st.H) o.st

/-- The invariant accepts every value and every memory local, and reads the
global state through its storage alone: what a call's arguments, return
variables and decoded data, and a frame's allocation, need. -/
structure ValMemOk (I : RunInv C) : Prop where
  val : ∀ H p v, I.loc H (.val p) v
  mem : ∀ H R v, I.loc H (.mem R) v
  glob : ∀ H H' (τ τ' : Semantics.State), τ'.storage = τ.storage → I.glob H τ → I.glob H' τ'

theorem TKeeps.drop {Γ Δ Δ' : Ctx} {t : TStep C Γ Δ} (hf : I.TKeeps t) (x : Ext Δ' Δ) :
    I.TKeeps (fun σ => (t σ).map fun o => ⟨o.st.drop x, o.ext⟩) := by
  intro σ o hσ h
  obtain ⟨o₁, hr, rfl⟩ := tmap_ok_inv h
  exact (hf σ o₁ hσ hr).drop x

theorem tkeeps_seq {Γ Γ₁ Γ₂ : Ctx} {s : TStep C Γ Γ₁} {P : TStep C Γ₁ Γ₂} (hs : I.TKeeps s)
    (hP : I.TKeeps P) : I.TKeeps (TRun.seq s P) := by
  intro σ o hσ h
  unfold TRun.seq at h
  split at h
  · rename_i o₁ ho₁
    obtain ⟨o₂, hp, rfl⟩ := tmap_ok_inv h
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
  obtain ⟨v, _, h⟩ := tbind_ok_inv h
  split at h
  · exact hthn.drop h₁ σ o hσ h
  · exact hels.drop h₂ σ o hσ h

theorem tkeeps_block {Γ Γ₁ : Ctx} (x : Ext Γ Γ₁) {body : TStep C Γ Γ₁} (hb : I.TKeeps body) :
    I.TKeeps (TRun.block x body) :=
  hb.drop x

theorem tkeeps_require {Γ : Ctx} (c : Val C Γ .bool) : I.TKeeps (TRun.require c) := by
  intro σ o hσ h
  unfold TRun.require at h
  obtain ⟨v, _, h⟩ := tbind_ok_inv h
  split at h
  · cases h; exact hσ
  · cases h

theorem tkeeps_assert {Γ : Ctx} (c : Val C Γ .bool) : I.TKeeps (TRun.assert c) := by
  intro σ o hσ h
  unfold TRun.assert at h
  obtain ⟨v, _, h⟩ := tbind_ok_inv h
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
  refine TLoop.run_induct (P := fun o : Out C σ.H Γ => I.HoldsT (HTy.toHeapTy 0 o.st.H) o.st)
    (Q := fun r => ∀ o, r = .ok o → I.HoldsT (HTy.toHeapTy 0 o.st.H) o.st)
    hσ (fun τ h₁ => ?_) (fun _ h => nomatch h) _ h
  simp only [TLoop.step]
  rcases c.evalT τ.st with _ | b
  · exact fun _ h => nomatch h
  · cases b
    · exact fun _ h => by cases h; exact h₁
    · dsimp only
      cases hr : body τ.st with
      | error => exact fun _ h => nomatch h
      | ok τ' => exact (hb τ.st τ' h₁ hr).drop x

/-- A call keeps an invariant `ValMemOk` accepts when its body does: the
arguments are values, the frame's return variables values or a fresh
memory object, the storage as it was. -/
theorem tkeeps_call {Γ Γ' ps rs Γf : Ctx} (hI : I.ValMemOk) (args : Args C Γ ps)
    (ret : CallRet Γ rs Γ') (x : Ext (rs ++ ps) Γf) {body : TStep C (rs ++ ps) Γf}
    (hb : I.TKeeps body) : I.TKeeps (TRun.call args ret x body) := by
  intro σ o hσ h
  unfold TRun.call at h
  obtain ⟨a, _, h⟩ := tbind_ok_inv h
  dsimp only at h
  obtain ⟨o₂, hr, h⟩ := tbind_ok_inv h
  cases h
  have h₀ : I.HoldsT (HTy.toHeapTy 0 σ.H) (σ.withEnv a) :=
    hσ.withEnv (TEnv.All.of_valMem (hI.val _) (hI.mem _) (Args.valMem args) _)
  have h₁ : I.HoldsT (HTy.toHeapTy 0 (ret.enterT (σ.withEnv a)).st.H)
      (ret.enterT (σ.withEnv a)).st :=
    ⟨hI.glob _ _ (σ.withEnv a).globE _
      (congrArg Storage.erase (CallRet.enterT_storage ret (σ.withEnv a))) h₀.1,
      CallRet.enterT_env ret _ (hI.val _) (hI.mem _)
        (env_mono (HTy.toHeapTy_extends (ret.enterT (σ.withEnv a)).ext) h₀.2)⟩
  have h₂ := hb _ o₂ h₁ hr
  refine ⟨h₂.1, CallRet.leaveT_all ret (TEnv.All.wk _ ?_)
    (TEnv.All.take rs (TEnv.All.drop x h₂.2))⟩
  exact env_mono (HTy.toHeapTy_extends ((ret.enterT (σ.withEnv a)).ext.trans o₂.ext)) hσ.2

theorem tkeeps_tryCall {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} (hI : I.ValMemOk) (call : ExtCall C Γ)
    (rets : Binders ρ) (h₁ : Ext (ρ ++ Γ) Γ₁) {ok : TStep C (ρ ++ Γ) Γ₁}
    (h₂ : Ext Γ Γ₂) {err : TStep C Γ Γ₂} (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) {pnc : TStep C (κ ++ Γ) Γ₃}
    (h₄ : Ext Γ Γ₄) {other : TStep C Γ Γ₄}
    (hok : I.TKeeps ok) (herr : I.TKeeps err) (hpnc : I.TKeeps pnc) (hoth : I.TKeeps other) :
    I.TKeeps (TRun.tryCall call rets h₁ ok h₂ err code h₃ pnc h₄ other) := by
  intro σ o hσ h
  unfold TRun.tryCall at h
  split at h
  · cases h
  · obtain ⟨⟨r, rest⟩, _, h⟩ := tbind_ok_inv h
    refine hok.drop ((Ext.append Γ ρ).trans h₁) (σ.withEnv (TEnv.append ρ r σ.env)) o
      (hσ.withEnv (TEnv.All.append ρ ?_ hσ.2)) h
    exact TEnv.All.of_valMem (hI.val _) (hI.mem _) (Binders.valMem rets) _
  · exact herr.drop h₂ σ o hσ h
  · obtain ⟨r, _, h⟩ := tbind_ok_inv h
    refine hpnc.drop ((Ext.append Γ κ).trans h₃) (σ.withEnv (TEnv.append κ r σ.env)) o
      (hσ.withEnv (TEnv.All.append κ ?_ hσ.2)) h
    exact TEnv.All.of_valMem (hI.val _) (hI.mem _) (CodeBinder.valMem code) _
  · exact hoth.drop h₄ σ o hσ h

end RunInv

end Solidity
