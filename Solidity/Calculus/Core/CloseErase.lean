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
    fun _ hn => SemanticsProperties.lookupBy_setBy_ne (fun h => hn (h ▸ List.mem_singleton_self _)) _ _,
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
    cases h; exact SemanticsProperties.lookupBy_setBy_ne (fun hx => hy (hx ▸ List.mem_singleton_self _)) _ _
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
  | saveNet x => cases h; exact SemanticsProperties.lookupBy_setBy_ne (fun hx => hy (hx ▸ List.mem_singleton_self _)) _ _
  | saveNetMt x => cases h; exact SemanticsProperties.lookupBy_setBy_ne (fun hx => hy (hx ▸ List.mem_singleton_self _)) _ _
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

end Solidity.Core
