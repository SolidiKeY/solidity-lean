import Solidity.Calculus.Core.HoldsErase

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

/-! ## The formulas -/

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
    obtain ⟨rfl, hU, hUB, hBU, hφ⟩ := hφ
    have hE : ∀ τ, EnvAgreeExcept φ.bindNames τ τ₀ →
        Solidity.holds τ (.upd .box (U.erase ns) (φ.erase (U.names ns))) := fun τ hτ => by
      have h' := h τ hτ
      simp only [Fml.erase] at h'
      split at h'
      · rename_i hnil
        rw [hnil]
        exact h'
      · exact h'
    have hR := Upd.apply_erase hag U hU
    show Modality.afterC .box (holds · φ) (U.apply σ)
    cases hσ : U.apply σ with
    | error => trivial
    | ok σ' =>
      rw [hσ] at hR
      cases hτ₀ : Solidity.Upd.apply (U.erase ns) τ₀ with
      | error => rw [hτ₀] at hR; exact hR.elim
      | ok τ₀' =>
        rw [hτ₀] at hR
        refine holds_of_erase_valid φ hφ hBU hR fun τ' hτ' => ?_
        have h1 : Modality.after .box (Solidity.holds · (φ.erase (U.names ns)))
            (Solidity.Upd.apply (U.erase ns) (overlay φ.bindNames τ' τ₀)) :=
          hE (overlay φ.bindNames τ' τ₀) (agreeExcept_overlay _ _ _)
        have hfr := Upd.apply_frame (agreeExcept_overlay φ.bindNames τ' τ₀) (U.erase ns) hUB
        rw [hτ₀] at hfr
        revert h1 hfr
        cases hτ : Solidity.Upd.apply (U.erase ns) (overlay φ.bindNames τ' τ₀) with
        | error => intro _ hfr; exact hfr.elim
        | ok τ'' =>
          intro h1 hfr
          refine (holds_congr_full (agreeExcept_full (agreeExcept_trans hfr (agreeExcept_symm hτ'))
            fun y hy => ?_) _).1 h1
          rw [Upd.apply_keep _ (U.erase ns) hτ y (fun hm => hUB y hm hy), lookupBy_overlay, if_pos hy]
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
  | _, .bind x t φ, _, hφ, hB, _, τ₀, hag, h => fun v => by
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
