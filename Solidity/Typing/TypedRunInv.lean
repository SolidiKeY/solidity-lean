import Solidity.Typing.Soundness
import Solidity.Semantics.RunFrame

/-!
# Invariants of the typed run

`Typing/Soundness.lean`'s `RunInv` (a part on the storage, a part on each
local at its type) read of a typed state (`RunInv.HoldsT`: its storage, and
`TEnv.All` over its locals) and carried along the typed run
(`Semantics/Run.lean`): `RunInv.TKeeps t` says the step `t`, from a typed
state the invariant holds of, ends, if in a state, in one it holds of.  The
scopes (a branch, a block, a loop's iteration, a call's frame, a `try`'s
clause) only push and pop locals, so they keep any such invariant once their
sub-programs do (`tkeeps_ite` … `tkeeps_tryCall`, a loop by
`TLoop.run_induct`); a call's arguments, return variables and decoded data
are values, memory references or storage aliases, which every invariant here accepts
(`RunInv.ValMemOk`).  A statement without sub-programs is proved once for
every hereditary invariant (`Stmt.keeps_all`, `Typing/HeredRun.lean`), read
on `TRun.*`.
-/

namespace Solidity

variable {C : Contract}

theorem TRes.ofOpt_ok {α : Type} {x : Option α} {a : α} (h : TRes.ofOpt x = .ok a) :
    x = some a := by
  cases x with
  | none => exact nomatch h
  | some b => cases h; rfl

/-! ## Typed locals that satisfy a predicate -/

/-- Locals of value and memory types only. -/
def Ctx.ValMem : Ctx → Prop
  | [] => True
  | .val _ :: Γ => Ctx.ValMem Γ
  | .mem _ :: Γ => Ctx.ValMem Γ
  | _ :: _ => False

/-- Every local of `e` satisfies `P` at its type. -/
def TEnv.All {H : HTy} (P : (t : LTy) → t.TDenote C H → Prop) : {Γ : Ctx} → TEnv C H Γ → Prop
  | [], _ => True
  | t :: _, e => P t e.1 ∧ TEnv.All P e.2

namespace TEnv.All

variable {H : HTy} {P : (t : LTy) → t.TDenote C H → Prop}

theorem mono {Q : (t : LTy) → t.TDenote C H → Prop}
    (hPQ : ∀ t v, P t v → Q t v) : {Γ : Ctx} → {e : TEnv C H Γ} → TEnv.All P e → TEnv.All Q e
  | [], _, _ => trivial
  | _ :: _, _, he => ⟨hPQ _ _ he.1, mono hPQ he.2⟩

theorem get {Γ : Ctx} {t : LTy} (i : Idx Γ t) : {e : TEnv C H Γ} → TEnv.All P e →
    P t (TEnv.get i e) := by
  induction i with
  | here => intro e h; exact h.1
  | there i ih => intro e h; exact ih h.2

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
    TEnv.All P e → P t v → TEnv.All P (TEnv.set i v e) := by
  intro Γ t i
  induction i with
  | here => intro e v h hv; exact ⟨hv, h.2⟩
  | there i ih => intro e v h hv; exact ⟨h.1, ih h.2 hv⟩

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

theorem Args.env_all {Γ : Ctx} {H : HTy}
    {P : (t : LTy) → t.TDenote C H → Prop}
    (hv : ∀ p v, P (.val p) v) (hm : ∀ R v, P (.mem R) v)
    (ha : ∀ R v, P (.alias R) v) :
    {ps : Ctx} → Args C Γ ps → (e : TEnv C H ps) → TEnv.All P e
  | _, .nil, _ => trivial
  | _, .snoc as _ _ _, e => ⟨hv _ _, Args.env_all hv hm ha as e.2⟩
  | _, .snocStorage as _ _ _, e => ⟨ha _ _, Args.env_all hv hm ha as e.2⟩
  | _, .snocMemory as _ _ _, e => ⟨hm _ _, Args.env_all hv hm ha as e.2⟩

theorem Binders.valMem : {ρ : Ctx} → Binders ρ → Ctx.ValMem ρ
  | _, .nil => trivial
  | .val _ :: ρ, .snoc bs _ _ => (Binders.valMem bs : Ctx.ValMem ρ)

theorem CodeBinder.valMem {κ : Ctx} (code : CodeBinder κ) : Ctx.ValMem κ := by
  cases code <;> trivial

/-- Leaving a call keeps every local satisfying `P` when the caller's and the
frame's return variables do. -/
theorem CallRet.leaveT_all {H : HTy} {P : (t : LTy) → t.TDenote C H → Prop} {Γ rs Γ' : Ctx}
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
  | storage R x => exact ⟨hr.1, he⟩

/-- Entering a call leaves the storage alone. -/
theorem CallRet.enterT_storage {Γ rs Γ' ps : Ctx} (ret : CallRet Γ rs Γ') (τ : State C ps) :
    (ret.enterT τ).st.storage = τ.storage := by
  cases ret <;> rfl

/-! ## Invariants of the typed run -/

namespace RunInv

variable {I : RunInv C}

/-- The caller's locals, weakened along the heap a step grew. -/
theorem env_wk {H H' : HTy} (x : H <+: H') : {Γ : Ctx} → {e : TEnv C H Γ} →
    TEnv.All I.loc e → TEnv.All I.loc (TEnv.wk x Γ e)
  | [], _, _ => trivial
  | _ :: _, _, he => ⟨I.loc_wk x he.1, env_wk x he.2⟩

/-- Entering a call: value returns, a fresh memory object or an unset storage
alias, on top of the parameters. -/
theorem enterT_env (hv : ∀ H p v, I.loc (H := H) (.val p) v)
    (hm : ∀ H R v, I.loc (H := H) (.mem R) v)
    (ha : ∀ H R, I.loc (H := H) (.alias R) none) {Γ rs Γ' ps : Ctx}
    (ret : CallRet Γ rs Γ') (τ : State C ps) (he : TEnv.All I.loc τ.env) :
    TEnv.All I.loc (ret.enterT τ).st.env := by
  cases ret with
  | none => exact he
  | val p x res => exact ⟨hv _ _ _, he⟩
  | rets bs =>
    exact TEnv.All.append _ (TEnv.All.of_valMem (hv _) (hm _) (Binders.valMem bs) _) he
  | mem R x hd hm' => exact ⟨hm _ _ _, env_wk _ he⟩
  | storage R x => exact ⟨ha _ _, he⟩

/-- The invariant holds of a typed state: of its storage, and of each local
at its type. -/
def HoldsT (I : RunInv C) {Γ : Ctx} (σ : State C Γ) : Prop :=
  I.glob σ.storage ∧ TEnv.All I.loc σ.env

/-- The locals replaced. -/
theorem HoldsT.withEnv {Γ Δ : Ctx} {σ : State C Γ} (h : I.HoldsT σ)
    {e : TEnv C σ.H Δ} (he : TEnv.All I.loc e) : I.HoldsT (σ.withEnv e) :=
  ⟨h.1, he⟩

theorem HoldsT.drop {Γ Δ : Ctx} {σ : State C Δ} (h : I.HoldsT σ) (x : Ext Γ Δ) :
    I.HoldsT (σ.drop x) :=
  ⟨h.1, TEnv.All.drop x h.2⟩

theorem HoldsT.setLocal {Γ : Ctx} {σ : State C Γ} (h : I.HoldsT σ) {t : LTy}
    (i : Idx Γ t) {v : t.TDenote C σ.H} (hv : I.loc t v) : I.HoldsT (σ.setLocal i v) :=
  ⟨h.1, TEnv.All.set i h.2 hv⟩

theorem HoldsT.push {Γ : Ctx} {σ : State C Γ} (h : I.HoldsT σ) {t : LTy}
    {v : t.TDenote C σ.H} (hv : I.loc t v) : I.HoldsT (σ.push v) :=
  ⟨h.1, hv, h.2⟩

/-- The storage replaced by one the invariant holds of. -/
theorem HoldsT.withStorage {Γ : Ctx} {σ : State C Γ} (h : I.HoldsT σ) {st : Storage C}
    (hs : I.glob st) : I.HoldsT (σ.withStorage st) :=
  ⟨hs, h.2⟩

/-- A grown heap adopted: the locals weakened along it. -/
theorem HoldsT.adopt {Γ : Ctx} {σ : State C Γ} {α : HTy → Type} (h : I.HoldsT σ)
    (g : Grown σ.H α) : I.HoldsT (σ.adopt g).1 :=
  ⟨h.1, env_wk g.ext h.2⟩

/-- A typed step keeps the invariant: from a typed state it holds of, the
step ends, if in a state, in one it holds of. -/
def TKeeps {Γ Γ' : Ctx} (I : RunInv C) (t : TStep C Γ Γ') : Prop :=
  ∀ (σ : State C Γ) (o : Out C σ.H Γ'), I.HoldsT σ → t σ = .ok o → I.HoldsT o.st

/-- The invariant accepts values, memory locals and storage aliases: what
call frames, arguments and decoded external data need. -/
structure ValMemOk (I : RunInv C) : Prop where
  val : ∀ H p v, I.loc (H := H) (.val p) v
  mem : ∀ H R v, I.loc (H := H) (.mem R) v
  alias : ∀ H R v, I.loc (H := H) (.alias R) v

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

theorem tkeeps_exhausted {Γ : Ctx} :
    I.TKeeps (fun _ : State C Γ => (.error .exhausted : TRes (Out C _ Γ))) :=
  fun _ _ _ h => nomatch h

theorem tkeeps_loop {Γ Γ₁ : Ctx} (c : Val C Γ .bool) (x : Ext Γ Γ₁) {body : TStep C Γ Γ₁}
    (hb : I.TKeeps body) : I.TKeeps (TRun.loop c x body) := by
  intro σ o hσ h
  unfold TRun.loop at h
  refine TLoop.run_induct (P := fun o : Out C σ.H Γ => I.HoldsT o.st)
    (Q := fun r => ∀ o, r = .ok o → I.HoldsT o.st)
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
arguments are values or references, its returns are values, a fresh memory object or an
unset alias, and entry keeps storage as it was. -/
theorem tkeeps_call {Γ Γ' ps rs Γf : Ctx} (hI : I.ValMemOk) (args : Args C Γ ps)
    (ret : CallRet Γ rs Γ') (x : Ext (rs ++ ps) Γf) {body : TStep C (rs ++ ps) Γf}
    (hb : I.TKeeps body) : I.TKeeps (TRun.call args ret x body) := by
  intro σ o hσ h
  unfold TRun.call at h
  obtain ⟨a, _, h⟩ := tbind_ok_inv h
  dsimp only at h
  obtain ⟨o₂, hr, h⟩ := tbind_ok_inv h
  cases h
  have h₀ : I.HoldsT (σ.withEnv a) :=
    hσ.withEnv (Args.env_all (hI.val _) (hI.mem _) (hI.alias _) args _)
  have h₁ : I.HoldsT (ret.enterT (σ.withEnv a)).st :=
    ⟨by rw [CallRet.enterT_storage]; exact h₀.1,
      enterT_env hI.val hI.mem (fun H R => hI.alias H R none) ret _ h₀.2⟩
  have h₂ := hb _ o₂ h₁ hr
  exact ⟨h₂.1, CallRet.leaveT_all ret (env_wk _ hσ.2)
    (TEnv.All.take rs (TEnv.All.drop x h₂.2))⟩

theorem tkeeps_tryCall {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (hI : I.ValMemOk) (call : ExtCall C Γ)
    (rets : Binders ρ) (h₁ : Ext (ρ ++ Γ) Γ₁) {ok : TStep C (ρ ++ Γ) Γ₁}
    (h₂ : Ext Γ Γ₂) {err : TStep C Γ Γ₂} (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) {pnc : TStep C (κ ++ Γ) Γ₃}
    (h₄ : Ext Γ Γ₄) {other : TStep C Γ Γ₄} (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf)
    {sbody : TStep C (ρ ++ ps) Γf} (self : Bool)
    (hok : I.TKeeps ok) (herr : I.TKeeps err) (hpnc : I.TKeeps pnc) (hoth : I.TKeeps other)
    (hsb : I.TKeeps sbody) :
    I.TKeeps (TRun.tryCall call rets h₁ ok h₂ err code h₃ pnc h₄ other sargs hs sbody self) := by
  intro σ o hσ h
  unfold TRun.tryCall at h
  have hp : ∀ c, I.HoldsT (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) c) σ.env)) :=
    fun _ => hσ.withEnv (TEnv.All.append κ
      (TEnv.All.of_valMem (hI.val _) (hI.mem _) (CodeBinder.valMem code) _) hσ.2)
  split at h
  · cases h
  split at h
  · split at h
    · rename_i o₁ hc
      have h1 := tkeeps_call hI sargs (.rets rets) hs hsb σ o₁ hσ hc
      cases hr : ok o₁.st with
      | error => rw [hr] at h; cases h
      | ok o' => rw [hr] at h; cases h; exact (hok _ o' h1 hr).drop _
    · exact hoth.drop h₄ σ o hσ h
    · split at h
      · exact herr.drop h₂ σ o hσ h
      · split at h
        · exact hpnc.drop ((Ext.append Γ κ).trans h₃) _ o (hp _) h
        · exact hoth.drop h₄ σ o hσ h
    · exact hpnc.drop ((Ext.append Γ κ).trans h₃) _ o (hp _) h
    · cases h
  split at h
  · cases h
  · obtain ⟨⟨r, rest⟩, _, h⟩ := tbind_ok_inv h
    refine hok.drop ((Ext.append Γ ρ).trans h₁) (σ.withEnv (TEnv.append ρ r σ.env)) o
      (hσ.withEnv (TEnv.All.append ρ ?_ hσ.2)) h
    exact TEnv.All.of_valMem (hI.val _) (hI.mem _) (Binders.valMem rets) _
  · exact herr.drop h₂ σ o hσ h
  · exact hpnc.drop ((Ext.append Γ κ).trans h₃) _ o (hp _) h
  · exact hoth.drop h₄ σ o hσ h

end RunInv

end Solidity
