import Solidity.Calculus.Core.HoldsErase
import Solidity.Typing.Soundness

/-!
# A goal closed by its erasure's validity

`holds_of_erase_valid`: a scoped formula holds where its erasure
(`Fml.erase`) is valid, for `Fml.Closable` formulas (`Calculus/Core/Closable.lean`),
the one-way condition a leaf of the strategy meets: its context puts hidden
binders and anonymising updates in positive positions, where `holds_erase`'s
two-way reading fails (`Calculus/Core/HoldsErase.lean`'s last section).  The
erasure reads a hidden binder's local at whatever the untyped state binds
it to, so its validity covers every value; the names a hidden binder binds
are carried as untyped states that differ there (`EnvAgreeExcept`), and the
updates above it leave those names alone (`Upd.apply_keep`).  `Proves.close`
(`Calculus/Core/Proves.lean`) is this, behind a context.
-/

namespace Solidity.Core

open Semantics (Value Res Binding lookupBy setBy EnvAgreeExcept ResultsAgree)
open Solidity (Modality Avoids)

variable {C : Contract}

/-! ## Untyped states that differ on some names -/

section Untyped

/-- `t` with the names `B` bound as `s` binds them. -/
abbrev overlay (B : List Var) (s t : Semantics.State) : Semantics.State :=
  t.anon B fun y => lookupBy y s.env

theorem lookupBy_overlay (B : List Var) (s t : Semantics.State) (y : Var) :
    lookupBy y (overlay B s t).env = if y ∈ B then lookupBy y s.env else lookupBy y t.env :=
  lookupBy_anonEnv _ y B t.env

theorem agreeExcept_refl (B : List Var) (s : Semantics.State) : EnvAgreeExcept B s s :=
  Semantics.EnvAgreeExcept.refl B s

theorem agreeExcept_symm {B : List Var} {s t : Semantics.State} (h : EnvAgreeExcept B s t) :
    EnvAgreeExcept B t s :=
  ⟨h.storage.symm, h.heap.symm, h.nextId.symm, h.net.symm, fun n hn => (h.env n hn).symm,
    h.selfBalance.symm, h.tx.symm⟩

theorem agreeExcept_trans {B : List Var} {s t u : Semantics.State} (h₁ : EnvAgreeExcept B s t)
    (h₂ : EnvAgreeExcept B t u) : EnvAgreeExcept B s u :=
  ⟨h₁.storage.trans h₂.storage, h₁.heap.trans h₂.heap, h₁.nextId.trans h₂.nextId,
    h₁.net.trans h₂.net, fun n hn => (h₁.env n hn).trans (h₂.env n hn),
    h₁.selfBalance.trans h₂.selfBalance, h₁.tx.trans h₂.tx⟩

theorem agreeExcept_mono {B B' : List Var} {s t : Semantics.State} (h : EnvAgreeExcept B s t)
    (hB : ∀ y ∈ B, y ∈ B') : EnvAgreeExcept B' s t :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun n hn => h.env n fun hm => hn (hB n hm),
    h.selfBalance, h.tx⟩

/-- Agreeing off `B`, and on `B` too: agreeing everywhere. -/
theorem agreeExcept_full {B : List Var} {s t : Semantics.State} (h : EnvAgreeExcept B s t)
    (hB : ∀ y ∈ B, lookupBy y s.env = lookupBy y t.env) : EnvAgreeExcept [] s t :=
  ⟨h.storage, h.heap, h.nextId, h.net,
    fun n _ => if hn : n ∈ B then hB n hn else h.env n hn, h.selfBalance, h.tx⟩

theorem agreeExcept_overlay (B : List Var) (s t : Semantics.State) :
    EnvAgreeExcept B (overlay B s t) t :=
  ⟨rfl, rfl, rfl, rfl, fun n hn => by rw [lookupBy_overlay, if_neg hn], rfl, rfl⟩

theorem agreeExcept_setEnv (s : Semantics.State) (x : Var) (b : Binding) :
    EnvAgreeExcept [x] (s.setEnv x b) s :=
  ⟨rfl, rfl, rfl, rfl,
    fun _ hn => SemanticsProperties.lookupBy_setBy_ne (fun h => hn (List.mem_singleton.mpr h)) _ _,
    rfl, rfl⟩

/-- States that agree everywhere satisfy the same formulas. -/
theorem holds_congr_full {s t : Semantics.State} (h : EnvAgreeExcept [] s t) (φ : Solidity.Fml C) :
    Solidity.holds s φ ↔ Solidity.holds t φ :=
  Solidity.holds_frame φ (fun _ _ => List.not_mem_nil) h

/-- An elementary update leaves a name it does not mention. -/
theorem UpdElem.write_keep (σ₀ : Semantics.State) (e : Solidity.UpdElem C)
    {τ τ' : Semantics.State} (h : e.write σ₀ τ = .ok τ') {y : Var} (hy : y ∉ e.vars) :
    lookupBy y τ'.env = lookupBy y τ.env := by
  have hne : ∀ {x : Var} {vs : List Var}, y ∉ x :: vs → y ≠ x := fun h hx => h (hx ▸ List.mem_cons_self)
  cases e with
  | val x t =>
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h; cases h
    exact SemanticsProperties.lookupBy_setBy_ne (hne hy) _ _
  | path x p =>
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h; cases h
    exact SemanticsProperties.lookupBy_setBy_ne (hne hy) _ _
  | unset x =>
    cases h; exact SemanticsProperties.lookupBy_setBy_ne (fun hx => hy (List.mem_singleton.mpr hx)) _ _
  | mref x i =>
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h; cases h
    exact SemanticsProperties.lookupBy_setBy_ne (hne hy) _ _
  | storage s => obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h; cases h; rfl
  | store x s =>
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h; cases h
    exact SemanticsProperties.lookupBy_setBy_ne (hne hy) _ _
  | memory m => obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h; cases h; rfl
  | selfBalance op a =>
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h; cases h; rfl
  | net r op a =>
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h; cases h; rfl
  | pay r a =>
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h
    split at h
    · exact nomatch h
    · cases h; rfl
  | saveNet x => cases h; exact SemanticsProperties.lookupBy_setBy_ne (fun hx => hy (List.mem_singleton.mpr hx)) _ _
  | saveNetMt x => cases h; exact SemanticsProperties.lookupBy_setBy_ne (fun hx => hy (List.mem_singleton.mpr hx)) _ _
  | netMt r a =>
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h; cases h; rfl
  | setBalance a =>
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨_, _, h⟩ := Semantics.bind_ok_inv h; cases h; rfl

/-- An update leaves a name it does not mention. -/
theorem Upd.apply_keep (σ₀ : Semantics.State) :
    (U : Solidity.Upd C) → {τ τ' : Semantics.State} →
      U.foldlM (fun τ e => e.write σ₀ τ) τ = .ok τ' → ∀ y, y ∉ Solidity.Upd.vars U →
        lookupBy y τ'.env = lookupBy y τ.env
  | [], _, _, h, _, _ => by cases h; rfl
  | e :: U, τ, τ', h, y, hy => by
    rw [List.foldlM_cons] at h
    obtain ⟨τ₁, h₁, h⟩ := Semantics.bind_ok_inv h
    have hy' : y ∉ e.vars ∧ y ∉ Solidity.Upd.vars U := by
      simp only [Solidity.Upd.vars, List.mem_append, not_or] at hy; exact hy
    exact (Upd.apply_keep σ₀ U h y hy'.2).trans (UpdElem.write_keep σ₀ e h₁ hy'.1)

end Untyped

/-! ## A diamond update that keeps the `bool` locals `bool`s -/

theorem Tm.boolB_eval {Γ : Ctx} {σ : State C Γ} (hT : σ.BoolOK) :
    (t : Tm C Γ .val) → t.boolB = true → ∀ {v : Semantics.Value}, t.eval σ = .ok v → ∃ b, v = .bool b
  | .app2 (.binop op p) a b, hb, v, h => by
    have hb' : (!op.isArith) = true := hb
    have hop : op.isArith = false := by simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using hb'
    change (do Solidity.evalBinop op p (← a.eval σ) (b.eval σ)) = .ok v at h
    obtain ⟨lv, -, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    unfold Solidity.evalBinop at h
    split at h
    · cases h; exact ⟨_, rfl⟩
    · cases h; exact ⟨_, rfl⟩
    · obtain ⟨rv, -, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
      obtain ⟨w, hw, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
      obtain ⟨c, rfl⟩ := applyBinOp_nonarith_bool hop hw
      cases h
      exact ⟨c, rfl⟩
  | .app1 (.unop .not p) _ a, _, v, h => by
    change (do Solidity.unopCheck .not p (← Semantics.applyUnOp .not (← a.eval σ))) = .ok v at h
    obtain ⟨x, -, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    obtain ⟨w, hw, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    simp only [Semantics.applyUnOp, bind, Except.bind] at hw
    split at hw
    · cases hw
    · cases hw
      cases h
      exact ⟨_, rfl⟩
  | .app0 (.lit (.bool c)), _, v, h => by cases h; exact ⟨c, rfl⟩
  | .pvV (p := .bool) i, _, v, h => by cases h; exact hT.get i

theorem Rhs.boolB_eval {Γ : Ctx} {σ : State C Γ} (hT : σ.BoolOK) :
    {t : LTy} → (r : Rhs C Γ t) → r.boolB = true → ∀ {v : t.Denote C}, r.eval σ = .ok v →
      LTy.BoolOK t v
  | _, .val (p := .bool) t, hb, _, h => Tm.boolB_eval hT t hb h
  | _, .val (p := .uint) _, _, _, _ | _, .val (p := .int) _, _, _, _ => trivial
  | _, .path _, _, _, _ | _, .unset, _, _, _ | _, .mref _, _, _, _ | _, .store _, _, _, _
  | _, .saveNet, _, _, _ | _, .saveNetMt, _, _, _ => trivial

theorem UpdElem.write_boolOK {Γ Δ : Ctx} {σ₀ : State C Γ} (h₀ : σ₀.BoolOK) (e : UpdElem C Γ Δ)
    (he : e.boolB = true) {τ τ' : State C Δ} (hτ : τ.BoolOK) (h : e.write σ₀ τ = .ok τ') :
    τ'.BoolOK := by
  cases e with
  | «local» i r =>
    change (do pure (τ.setLocal i (← r.eval σ₀))) = .ok τ' at h
    obtain ⟨v, hv, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    cases h
    exact hτ.setLocal i (Rhs.boolB_eval h₀ r he hv)
  | _ =>
    simp only [UpdElem.write, bind, Except.bind, pure, Except.pure] at h
    repeat' split at h
    all_goals first | (cases h; exact hτ.withGlob _) | cases h

theorem Upd.apply_boolOK {Γ : Ctx} {σ₀ : State C Γ} (h₀ : σ₀.BoolOK) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → U.boolB = true → ∀ {τ : State C Δ}, U.apply σ₀ = .ok τ →
      τ.BoolOK
  | _, .nil, _, _, h => by cases h; exact h₀
  | _, .snoc U e, hb, _, h => by
    have hb' : U.boolB = true ∧ e.boolB = true := Bool.and_eq_true _ _ ▸ hb
    change (do e.write σ₀ (← U.apply σ₀)) = .ok _ at h
    obtain ⟨τ₁, h₁, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    exact UpdElem.write_boolOK h₀ e hb'.2 (Upd.apply_boolOK h₀ U hb'.1 h₁) h
  | _, .decl U _ r, hb, _, h => by
    have hb' : U.boolB = true ∧ r.boolB = true := Bool.and_eq_true _ _ ▸ hb
    change (do let τ ← U.apply σ₀; pure (τ.push (← r.eval σ₀))) = .ok _ at h
    obtain ⟨τ₁, h₁, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    obtain ⟨v, hv, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    cases h
    exact (Upd.apply_boolOK h₀ U hb'.1 h₁).push (Rhs.boolB_eval h₀ r hb'.2 hv)
  | _, .pop U e, hb, _, h => by
    change (U.apply σ₀).map (State.drop e) = .ok _ at h
    cases h₁ : U.apply σ₀ with
    | error => rw [h₁] at h; cases h
    | ok τ₁ =>
      rw [h₁] at h; cases h
      exact (Upd.apply_boolOK h₀ U hb h₁).drop e
  | _, .drop U e, hb, _, h => by
    change (U.apply σ₀).map (State.thin e) = .ok _ at h
    cases h₁ : U.apply σ₀ with
    | error => rw [h₁] at h; cases h
    | ok τ₁ =>
      rw [h₁] at h; cases h
      exact (Upd.apply_boolOK h₀ U hb h₁).thin e

/-! ## The formulas -/

theorem erase_upd_holds {Γ Δ : Ctx} {ns : List Var} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ}
    {τ : Semantics.State} :
    Solidity.holds τ (Fml.erase ns (.upd m U φ)) ↔
      m.after (Solidity.holds · (φ.erase (U.names ns))) (Solidity.Upd.apply (U.erase ns) τ) := by
  simp only [Fml.erase]
  split
  · rename_i h
    rw [h]
    rfl
  · rfl


/-- Agreement survives a change of the untyped state off the scope's names. -/
theorem Agree.congrExcept {Γ : Ctx} {ns B : List Var} {σ : State C Γ} {τ₀ τ : Semantics.State}
    (hag : Agree ns σ τ₀) (h : EnvAgreeExcept B τ τ₀) (hB : Avoids B ns) : Agree ns σ τ where
  len := hag.len
  nodup := hag.nodup
  glob := by
    show withLocals (withLocals σ.glob τ₀.env) τ.env = τ
    rw [hag.glob]
    obtain ⟨hs, hh, hn, hnet, -, hsb, htx⟩ := h
    cases τ; cases τ₀
    simp only at hs hh hn hnet hsb htx
    subst hs hh hn hnet hsb htx
    rfl
  env := fun ⟨x, b⟩ hm => by
    rw [h.env x fun hx => hB x hx (Env.mem_erase_key hm)]
    exact hag.env _ hm

/-- **A goal closed by its erasure's validity**: a `Fml.Closable` formula
holds in `σ` when its erasure holds in every untyped state that agrees with
one agreeing with `σ` off the names its hidden binders bind. -/
theorem holds_of_erase_valid : {Γ : Ctx} → (φ : Fml C Γ) → {ns : List Var} → φ.Closable ns →
    Avoids φ.bindNames ns → {σ : State C Γ} → {τ₀ : Semantics.State} → Agree ns σ τ₀ →
    (∀ τ, EnvAgreeExcept φ.bindNames τ τ₀ → Solidity.holds τ (φ.erase ns)) → holds σ φ
  | _, .tt, _, _, _, _, _, _, _ => trivial
  | _, .eq a b, _, _, _, _, τ₀, hag, h =>
    (holds_erase (.eq a b) trivial hag).2 (h τ₀ (agreeExcept_refl _ τ₀))
  | _, .defined t, _, _, _, _, τ₀, hag, h =>
    (holds_erase (.defined t) trivial hag).2 (h τ₀ (agreeExcept_refl _ τ₀))
  | _, .not φ, _, hφ, _, _, τ₀, hag, h =>
    (holds_erase (.not φ) hφ hag).2 (h τ₀ (agreeExcept_refl _ τ₀))
  | _, .modal m P κ φ, _, hφ, _, _, τ₀, hag, h =>
    (holds_erase (.modal m P κ φ) hφ hag).2 (h τ₀ (agreeExcept_refl _ τ₀))
  | _, .and φ ψ, _, hφ, hB, _, _, hag, h =>
    ⟨holds_of_erase_valid φ hφ.1 (Avoids.left hB) hag fun τ hτ =>
        (h τ (agreeExcept_mono hτ fun _ hy => List.mem_append_left _ hy)).1,
      holds_of_erase_valid ψ hφ.2 (Avoids.right hB) hag fun τ hτ =>
        (h τ (agreeExcept_mono hτ fun _ hy => List.mem_append_right _ hy)).2⟩
  | _, .imp φ ψ, _, hφ, hB, _, _, hag, h => fun ha =>
    holds_of_erase_valid ψ hφ.2 hB hag fun τ hτ =>
      h τ hτ ((holds_erase φ hφ.1 (hag.congrExcept hτ hB)).1 ha)
  | _, .upd m U φ, ns, hφ, _, σ, τ₀, hag, h => by
    obtain ⟨hm, hU, hUB, hBU, hφ⟩ := hφ
    have hE : ∀ τ, EnvAgreeExcept φ.bindNames τ τ₀ →
        m.after (Solidity.holds · (φ.erase (U.names ns))) (Solidity.Upd.apply (U.erase ns) τ) :=
      fun τ hτ => erase_upd_holds.1 (h τ hτ)
    have hR := Upd.apply_erase hag U hU
    have core : m.afterC (holds · φ) (U.apply σ) := by
      have H₀ := hE τ₀ (agreeExcept_refl _ τ₀)
      revert hR H₀
      cases U.apply σ with
      | error =>
        cases Solidity.Upd.apply (U.erase ns) τ₀ with
        | error => intro _ H₀; exact H₀
        | ok => intro hR; exact hR.elim
      | ok σ' =>
        cases hτ₀ : Solidity.Upd.apply (U.erase ns) τ₀ with
        | error => intro hR; exact hR.elim
        | ok τ₀' =>
          intro hR _
          refine holds_of_erase_valid φ hφ hBU hR fun τ' hτ' => ?_
          have h1 := hE (overlay φ.bindNames τ' τ₀) (agreeExcept_overlay _ _ _)
          have hfr := Upd.apply_frame (agreeExcept_overlay φ.bindNames τ' τ₀) (U.erase ns) hUB
          rw [hτ₀] at hfr
          revert h1 hfr
          cases hτ : Solidity.Upd.apply (U.erase ns) (overlay φ.bindNames τ' τ₀) with
          | error => intro _ hfr; exact hfr.elim
          | ok τ'' =>
            intro h1 hfr
            refine (holds_congr_full (agreeExcept_full (agreeExcept_trans hfr (agreeExcept_symm hτ'))
              fun y hy => ?_) _).1 h1
            rw [Upd.apply_keep _ (U.erase ns) hτ y (fun hm => hUB y hm hy), lookupBy_overlay,
              if_pos hy]
    refine holds_upd_intro fun hT => ?_
    cases m with
    | box => exact core
    | diamond =>
      have hb : U.boolB = true := hm.resolve_left nofun
      revert core
      cases hσ : U.apply σ with
      | error => exact id
      | ok σ₁ => exact fun hc => ⟨Upd.apply_boolOK (hT rfl) U hb hσ, hc⟩
  | _, .havoc φ, _, hφ, hB, σ, τ₀, hag, h => fun st nt => by
    have hag' := hag.withGlob (σ.glob.havoc st nt)
    have e : withLocals (σ.glob.havoc st nt) τ₀.env = τ₀.havoc st nt := by
      have hw := hag.wl
      generalize τ₀.env = env at hw ⊢
      subst hw
      rfl
    rw [e] at hag'
    refine holds_of_erase_valid φ hφ hB hag' fun τ' hτ' => ?_
    have h1 := h (overlay φ.bindNames τ' τ₀) (agreeExcept_overlay _ _ _) st nt
    refine (holds_congr_full (agreeExcept_full (agreeExcept_trans
      ((agreeExcept_overlay _ τ' τ₀).havoc st nt) (agreeExcept_symm hτ')) fun y hy => ?_) _).1 h1
    show lookupBy y (overlay _ τ' τ₀).env = _
    rw [lookupBy_overlay, if_pos hy]
  | _, .all x p φ, _, hφ, hB, _, τ₀, hag, h => fun v hv => by
    obtain ⟨hx, hxB, hφ⟩ := hφ
    refine holds_of_erase_valid φ hφ (fun y hy hm => ?_) (hag.push (t := .val p) hx v)
      fun τ' hτ' => ?_
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact hxB hy
      · exact hB y hy hm
    · have h1 := h (overlay φ.bindNames τ' τ₀) (agreeExcept_overlay _ _ _) v hv
      refine (holds_congr_full (agreeExcept_full (agreeExcept_trans
        ((agreeExcept_overlay _ τ' τ₀).setEnv_both x _) (agreeExcept_symm hτ')) fun y hy => ?_) _).1 h1
      have hne : y ≠ x := fun e => by subst e; exact hxB hy
      show lookupBy y (setBy x _ (overlay _ τ' τ₀).env) = _
      rw [SemanticsProperties.lookupBy_setBy_ne hne, lookupBy_overlay, if_pos hy]
  | _, .bind _ x t φ, _, hφ, hB, _, τ₀, hag, h => holds_bind_intro fun v => by
    obtain ⟨hx, hxB, hφ⟩ := hφ
    refine holds_of_erase_valid φ hφ (fun y hy hm => ?_) (hag.push hx v) fun τ' hτ' => ?_
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact hxB hy
      · exact hB y (List.mem_cons_of_mem _ hy) hm
    · exact h τ' (agreeExcept_trans (agreeExcept_mono hτ' fun _ hy => List.mem_cons_of_mem _ hy)
        (agreeExcept_mono (agreeExcept_setEnv τ₀ x _) fun _ hy => by
          rw [List.mem_singleton.1 hy]; exact List.mem_cons_self))
  | _, .anon xs φ, ns, hφ, hB, σ, τ₀, hag, h => fun b => by
    obtain ⟨τ₁, h₁, h₂⟩ := Agree.anon b xs hag
    have hag' : Agree ns (σ.anon xs b) (overlay (xs.map fun x => x.2.name ns) τ₁ τ₀) := by
      refine h₁.congrEnv ?_ fun y => ?_
      · rw [State.glob_anon b xs σ]
        have hw := hag.wl
        generalize τ₀.env = env at hw ⊢
        subst hw
        rfl
      · rw [lookupBy_overlay]
        split
        · rfl
        · exact (h₂ y ‹_›).symm
    refine holds_of_erase_valid φ hφ hB hag' fun τ' hτ' => ?_
    have h1 := h (overlay φ.bindNames τ' τ₀) (agreeExcept_overlay _ _ _) (fun y => lookupBy y τ'.env)
    have hys : ∀ y ∈ xs.map (fun x => x.2.name ns), y ∈ (xs.map fun x => x.2.name ns) ++ φ.bindNames :=
      fun _ hy => List.mem_append_left _ hy
    have hbs : ∀ y ∈ φ.bindNames, y ∈ (xs.map fun x => x.2.name ns) ++ φ.bindNames :=
      fun _ hy => List.mem_append_right _ hy
    refine (holds_congr_full (agreeExcept_full
      (agreeExcept_trans (agreeExcept_mono (agreeExcept_overlay _ τ' _) hys)
        (agreeExcept_trans (agreeExcept_mono (agreeExcept_overlay _ τ' τ₀) hbs)
          (agreeExcept_trans (agreeExcept_mono (agreeExcept_symm (agreeExcept_overlay _ τ₁ τ₀)) hys)
            (agreeExcept_mono (agreeExcept_symm hτ') hbs)))) fun y hy => ?_) _).1 h1
    show lookupBy y (overlay _ τ' (overlay _ τ' τ₀)).env = _
    rw [lookupBy_overlay, lookupBy_overlay]
    by_cases hy₁ : y ∈ xs.map (fun x => x.2.name ns)
    · rw [if_pos hy₁]
    · rw [if_neg hy₁, if_pos ((List.mem_append.1 hy).resolve_left hy₁)]

end Solidity.Core
