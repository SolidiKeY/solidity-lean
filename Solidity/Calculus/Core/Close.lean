import Solidity.Calculus.Core.HoldsErase
import Solidity.Calculus.Core.CloseErase
import Solidity.Calculus.Close

/-!
# Closing a scoped leaf by its erasure

What the scoped strategy leaves (`Core.symex`, `Calculus/Core/Step.lean`)
is closed by today's closer (Decision 6: `Fml.erase` is the bridge until
the closer is ported): a scoped formula is valid when its erasure is
(`Valid.of_erase`), and the erasure goes to `Close.lean`'s `sol_close` or to
`Derive.proves`, the closer `sol_prove` runs.

A first-order formula reads as its erasure (`holds_erase_fo`); a leaf has
more: updates, of either modality (the reading of an update asks only of
the typed states that erase to the state it ends in), and hidden binders
(`uint r = e;` binds `r`, `localValueDeclInitDrop`).  A hidden binder
erases to its body read at the name's current binding, which one untyped
state does not range over, but a valid erasure does: in every state, so
for every binding of the name.  The induction carries that as its
hypothesis: the erasure holds in every state that differs from the one at
hand only at the names `B` the binders below declare
(`holds_of_erase_pos`).  It goes through an update, a precondition or a
quantifier that does not mention those names, and through `{anon(…)}`,
whose untyped reading ranges over every binding of the names it anonymises
(a loop's frame, with the body's binders under it); `Fml.posB` checks this:
the binders sit outside negations and preconditions, what is negated or
assumed is first-order, and no update, precondition or quantifier names
them.  A leaf with a modality is not taken.

`posB` is evaluated by the kernel inside `sol_prove`'s check, so it is
written by `Fml.rec`, and the checks it calls by a recursor or by `casesOn`
with the motive generalising the index (Gate G0, condition 1), as the
strategy is.
-/

namespace Solidity.Core

open Semantics (EnvAgreeExcept ResultsAgree)
open Solidity (Modality)

variable {C : Contract}

/-! ## The checks

Each by the recursor, which the kernel unfolds with no `brecOn`, and a
compiled twin by `match` (`implemented_by`) for the tactics' first look. -/

/-- `Upd.freshK`'s compiled twin. -/
def Upd.freshM {Γ : Ctx} (ns : List Var) : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U _ => U.freshM ns
  | _, .decl U x _ => U.freshM ns && !(U.names ns).contains x
  | _, .pop U _ => U.freshM ns
  | _, .drop U _ => U.freshM ns

/-- Every local an update declares takes a name not in scope (`Upd.Fresh`):
`Closable.lean`'s `Upd.freshB` by `List.contains`, which the kernel evaluates
faster, with a compiled twin. -/
@[implemented_by Upd.freshM]
def Upd.freshK {Γ : Ctx} (ns : List Var) {Δ : Ctx} (U : Upd C Γ Δ) : Bool :=
  Upd.rec (motive := fun _ _ => Bool) true (fun _ _ ih => ih)
    (fun U x _ ih => ih && !(U.names ns).contains x) (fun _ _ ih => ih) (fun _ _ ih => ih) U

/-- `Fml.plainB`'s compiled twin. -/
def Fml.plainM : {Γ : Ctx} → Fml C Γ → List Var → Bool
  | _, .tt, _ | _, .eq .., _ | _, .defined _, _ => true
  | _, .not φ, ns => φ.plainM ns
  | _, .and φ ψ, ns | _, .imp φ ψ, ns => φ.plainM ns && ψ.plainM ns
  | _, .all x _ φ, ns => !ns.contains x && φ.plainM (x :: ns)
  | _, .upd .., _ | _, .havoc _, _ | _, .modal .., _ | _, .bind .., _ | _, .anon .., _ => false

/-- `Fml.Plain` and `Fml.FO`, decided: a first-order formula whose `∀`s bind
fresh names, which reads as its erasure both ways (`holds_erase_fo`). -/
@[implemented_by Fml.plainM]
def Fml.plainB {Γ : Ctx} (φ : Fml C Γ) : List Var → Bool :=
  Fml.rec (motive := fun _ _ => List Var → Bool)
    (tt := fun _ => true) (eq := fun _ _ _ => true) (defined := fun _ _ => true)
    (not := fun _ ih ns => ih ns)
    (and := fun _ _ ihφ ihψ ns => ihφ ns && ihψ ns)
    (imp := fun _ _ iha ihφ ns => iha ns && ihφ ns)
    (upd := fun _ _ _ _ _ => false)
    (modal := fun _ _ _ _ _ _ => false)
    (havoc := fun _ _ _ => false)
    (all := fun x _ _ ih ns => !ns.contains x && ih (x :: ns))
    (bind := fun _ _ _ _ _ _ => false) (anon := fun _ _ _ _ => false) φ

/-- No name of `vs` is in `B`. -/
def disjointB (B vs : List Var) : Bool := !vs.any B.contains

/-- `Fml.posB`'s compiled twin. -/
def Fml.posM : {Γ : Ctx} → Fml C Γ → List Var → Option (List Var)
  | _, .tt, _ | _, .eq .., _ | _, .defined _, _ => some []
  | _, .not φ, ns => if φ.plainB ns then some [] else none
  | _, .anon _ φ, ns => φ.posM ns
  | _, .and φ ψ, ns => (φ.posM ns).bind fun B₁ => (ψ.posM ns).map (B₁ ++ ·)
  | _, .imp a φ, ns =>
    if a.plainB ns then (φ.posM ns).bind fun B =>
      if disjointB B (a.erase ns).vars then some B else none
    else none
  | _, .upd _ U φ, ns =>
    if U.freshK ns then (φ.posM (U.names ns)).bind fun B =>
      if disjointB B (Solidity.Upd.vars (U.erase ns)) then some B else none
    else none
  | _, .modal .., _ => none
  | _, .havoc φ, ns => φ.posM ns
  | _, .all x _ φ, ns =>
    if ns.contains x then none
    else (φ.posM (x :: ns)).bind fun B => if B.contains x then none else some B
  | _, .bind _ x _ φ, ns => if ns.contains x then none else (φ.posM (x :: ns)).map (x :: ·)

/-- **A leaf closable by its erasure**: `some B`, `B` the names its hidden
binders declare, when they sit where `holds_of_erase_pos` takes them (no
binder under a negation, a precondition or a modality, but one under
`{anon(…)}` or an update of either modality taken; no update, precondition
or quantifier naming one; every binder fresh), and what is negated or
assumed is first-order (`Fml.plainB`); `none` otherwise. -/
@[implemented_by Fml.posM]
def Fml.posB {Γ : Ctx} (φ : Fml C Γ) : List Var → Option (List Var) :=
  Fml.rec (motive := fun _ _ => List Var → Option (List Var))
    (tt := fun _ => some []) (eq := fun _ _ _ => some []) (defined := fun _ _ => some [])
    (not := fun φ _ ns => if φ.plainB ns then some [] else none)
    (and := fun _ _ ihφ ihψ ns => (ihφ ns).bind fun B₁ => (ihψ ns).map (B₁ ++ ·))
    (imp := fun a _ _ ihφ ns =>
      if a.plainB ns then (ihφ ns).bind fun B =>
        if disjointB B (a.erase ns).vars then some B else none
      else none)
    (upd := fun _ U _ ih ns =>
      if U.freshK ns then (ih (U.names ns)).bind fun B =>
        if disjointB B (Solidity.Upd.vars (U.erase ns)) then some B else none
      else none)
    (modal := fun _ _ _ _ _ _ => none)
    (havoc := fun _ ih ns => ih ns)
    (all := fun x _ _ ih ns =>
      if ns.contains x then none
      else (ih (x :: ns)).bind fun B => if B.contains x then none else some B)
    (bind := fun _ x _ _ ih ns => if ns.contains x then none else (ih (x :: ns)).map (x :: ·))
    (anon := fun _ _ ih ns => ih ns) φ

/-! ## The checks are sound -/

theorem Upd.fresh_of_freshK {Γ : Ctx} (ns : List Var) {Δ : Ctx} (U : Upd C Γ Δ)
    (h : U.freshK ns = true) : U.Fresh ns := by
  induction U with
  | nil => trivial
  | snoc U _ ih => exact ih h
  | decl U x _ ih =>
    have h' : U.freshK ns = true ∧ (U.names ns).contains x = false := by
      simpa only [Upd.freshK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] using h
    exact ⟨ih h'.1, fun hx => by rw [List.contains_iff_mem.2 hx] at h'; cases h'.2⟩
  | pop U _ ih => exact ih h
  | drop U _ ih => exact ih h

theorem Fml.plain_of_plainB {Γ : Ctx} (φ : Fml C Γ) : ∀ {ns : List Var}, φ.plainB ns = true →
    φ.Plain ns ∧ φ.FO = true := by
  induction φ with
  | tt | eq | defined => intro _ _; exact ⟨trivial, rfl⟩
  | not φ ih => intro ns h; exact ih h
  | and φ ψ ihφ ihψ =>
    intro ns h
    have h' : φ.plainB ns = true ∧ ψ.plainB ns = true := Bool.and_eq_true _ _ ▸ h
    exact ⟨⟨(ihφ h'.1).1, (ihψ h'.2).1⟩, Bool.and_eq_true_iff.mpr ⟨(ihφ h'.1).2, (ihψ h'.2).2⟩⟩
  | imp a φ iha ihφ =>
    intro ns h
    have h' : a.plainB ns = true ∧ φ.plainB ns = true := Bool.and_eq_true _ _ ▸ h
    exact ⟨⟨(iha h'.1).1, (ihφ h'.2).1⟩, Bool.and_eq_true_iff.mpr ⟨(iha h'.1).2, (ihφ h'.2).2⟩⟩
  | upd | modal | havoc | bind | anon => intro _ h; cases h
  | all x p φ ih =>
    intro ns h
    have h' : (!ns.contains x) = true ∧ φ.plainB (x :: ns) = true := Bool.and_eq_true _ _ ▸ h
    refine ⟨⟨fun hx => ?_, (ih h'.2).1⟩, (ih h'.2).2⟩
    rw [List.contains_iff_mem.2 hx] at h'
    cases h'.1

theorem disjointB_avoids {B vs : List Var} (h : disjointB B vs = true) : Solidity.Avoids vs B := by
  intro x hx hB
  simp only [disjointB, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false] at h
  exact h x hx (List.contains_iff_mem.2 hB)

/-! ## Untyped states alike off some names -/

section Untyped

open Semantics

theorem envAgree_symm {ns : List Var} {σ τ : Semantics.State} (h : EnvAgreeExcept ns σ τ) :
    EnvAgreeExcept ns τ σ :=
  ⟨h.storage.symm, h.heap.symm, h.nextId.symm, h.net.symm, fun n hn => (h.env n hn).symm,
    h.selfBalance.symm, h.tx.symm⟩

/-- Two states alike but for their locals, whose lookups agree, satisfy the
same formulas. -/
theorem holds_of_envAgree_nil {φ : Solidity.Fml C} {σ τ : Semantics.State} (h : EnvAgreeExcept [] σ τ) :
    Solidity.holds σ φ → Solidity.holds τ φ :=
  (Solidity.holds_frame φ (fun _ _ => List.not_mem_nil) h).1

/-- `τ` with the names `B` bound as in `ρ`. -/
def mergeOn (B : List Var) (τ ρ : Semantics.State) : Semantics.State := τ.anon B fun y => lookupBy y ρ.env

theorem mergeOn_agree (B : List Var) (τ ρ : Semantics.State) : EnvAgreeExcept B τ (mergeOn B τ ρ) :=
  ⟨rfl, rfl, rfl, rfl, fun n hn => by
    simp only [mergeOn, Semantics.State.anon, lookupBy_anonEnv, hn, if_false], rfl, rfl⟩

theorem lookupBy_mergeOn {B : List Var} {τ ρ : Semantics.State} {y : Var} (hy : y ∈ B) :
    lookupBy y (mergeOn B τ ρ).env = lookupBy y ρ.env := by
  simp only [mergeOn, Semantics.State.anon, lookupBy_anonEnv, hy, if_true]

end Untyped

/-! ## The scoped side -/

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

/-- **A leaf holds where its erasure is valid off its binders' names**:
the erasure in every state that differs from `τ` only at `B` gives the
scoped formula in a typed state whose erasure agrees with `τ`. -/
theorem holds_of_erase_pos {Γ : Ctx} (φ : Fml C Γ) : ∀ {ns B : List Var}, φ.posB ns = some B →
    ∀ {σ : TState C Γ} {τ : Semantics.State}, Agree ns σ.erase τ →
    (∀ ρ, EnvAgreeExcept B τ ρ → Solidity.holds ρ (φ.erase ns)) → holds σ φ := by
  induction φ with
  | tt => intro _ _ _ _ _ _ _; trivial
  | eq a b =>
    intro ns B _ σ τ hag H
    exact (holds_erase_fo (.eq a b) trivial rfl hag).2 (H τ (Semantics.EnvAgreeExcept.refl _ _))
  | defined t =>
    intro ns B _ σ τ hag H
    exact (holds_erase_fo (.defined t) trivial rfl hag).2 (H τ (Semantics.EnvAgreeExcept.refl _ _))
  | not φ _ =>
    intro ns B h σ τ hag H
    have hp : φ.plainB ns = true := by
      cases hn : φ.plainB ns
      · simp only [Fml.posB, hn] at h; cases h
      · rfl
    have hp' := Fml.plain_of_plainB φ hp
    exact (holds_erase_fo (.not φ) hp'.1 hp'.2 hag).2 (H τ (Semantics.EnvAgreeExcept.refl _ _))
  | anon xs φ ih =>
    intro ns B h σ τ hag H
    change φ.posB ns = some B at h
    -- a binding of the anonymised locals, on both sides: `τ₁` is `τ` but at
    -- their names
    intro b
    obtain ⟨τ₁, h₁, h₂⟩ := Agree.anon (fun x => LTy.TDenote.erase x.1 (b x)) xs hag
    rw [← TState.anon_erase] at h₁
    have hτ₁ : withLocals σ.erase.glob τ₁.env = τ₁ := by
      have hg := h₁.glob
      rwa [TState.anon_erase, State.glob_anon _ xs σ.erase] at hg
    have hττ₁ : EnvAgreeExcept (xs.map fun x => x.2.name ns) τ τ₁ := by
      rw [← hag.glob, ← hτ₁]
      exact ⟨rfl, rfl, rfl, rfl, fun y hy => (h₂ y hy).symm, rfl, rfl⟩
    refine ih h h₁ fun ρ hρ => ?_
    -- `ρ` is `τ` with `B` as `ρ` has them, then the anonymised names as `ρ` has them
    have hτρ := Solidity.Semantics.EnvAgreeExcept.trans
      (Solidity.Semantics.EnvAgreeExcept.of_sub (fun _ hy => List.mem_append_left B hy) hττ₁)
      (Solidity.Semantics.EnvAgreeExcept.of_sub (fun _ hy => List.mem_append_right _ hy) hρ)
    have Hρ₀ : Solidity.holds ((mergeOn B τ ρ).anon (xs.map fun x => x.2.name ns)
        fun y => Semantics.lookupBy y ρ.env) (φ.erase ns) :=
      H (mergeOn B τ ρ) (mergeOn_agree B τ ρ) _
    refine holds_of_envAgree_nil (EnvAgreeExcept.mk (s₁ := (mergeOn B τ ρ).anon
      (xs.map fun x => x.2.name ns) fun y => Semantics.lookupBy y ρ.env) (s₂ := ρ)
      hτρ.storage hτρ.heap hτρ.nextId hτρ.net (fun y _ => ?_) hτρ.selfBalance hτρ.tx) Hρ₀
    simp only [Semantics.State.anon, lookupBy_anonEnv]
    split
    · rfl
    · rename_i hyn
      by_cases hyB : y ∈ B
      · exact lookupBy_mergeOn hyB
      · rw [← (mergeOn_agree B τ ρ).env y hyB]
        exact hτρ.env y fun hm => (List.mem_append.1 hm).elim hyn hyB
  | modal => intro _ _ h; cases h
  | and φ ψ ihφ ihψ =>
    intro ns B h σ τ hag H
    change (φ.posB ns).bind (fun B₁ => (ψ.posB ns).map (B₁ ++ ·)) = some B at h
    obtain ⟨B₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨B₂, h₂, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨ihφ h₁ hag fun ρ hρ =>
        (H ρ (Solidity.Semantics.EnvAgreeExcept.of_sub (fun _ hx => List.mem_append_left _ hx) hρ)).1,
      ihψ h₂ hag fun ρ hρ =>
        (H ρ (Solidity.Semantics.EnvAgreeExcept.of_sub (fun _ hx => List.mem_append_right _ hx) hρ)).2⟩
  | imp a φ _ ihφ =>
    intro ns B h σ τ hag H
    have ha : a.plainB ns = true := by
      cases hn : a.plainB ns
      · simp only [Fml.posB, hn] at h; cases h
      · rfl
    change (if a.plainB ns then (φ.posB ns).bind fun B =>
        if disjointB B (a.erase ns).vars then some B else none else none) = some B at h
    rw [if_pos ha] at h
    obtain ⟨B', h₁, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · cases h
      rename_i hd
      intro hσa
      have ha' := Fml.plain_of_plainB a ha
      have hτa := (holds_erase_fo a ha'.1 ha'.2 hag).1 hσa
      exact ihφ h₁ hag fun ρ hρ =>
        H ρ hρ ((Solidity.holds_frame (a.erase ns) (disjointB_avoids hd) hρ).1 hτa)
    · cases h
  | upd m U φ ih =>
    intro ns B h σ τ hag H
    change (if U.freshK ns then (φ.posB (U.names ns)).bind fun B =>
        if disjointB B (Solidity.Upd.vars (U.erase ns)) then some B else none else none) =
      some B at h
    have hU : U.freshK ns = true := by
      cases hn : U.freshK ns
      · rw [hn] at h; cases h
      · rfl
    rw [if_pos hU] at h
    obtain ⟨B', h₁, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · cases h
      rename_i hd
      have hav := disjointB_avoids hd
      have hrel := Upd.apply_erase hag U (Upd.fresh_of_freshK ns U hU)
      have H₀ := erase_upd_holds.1 (H τ (Semantics.EnvAgreeExcept.refl _ _))
      show m.afterC (fun τ' => ∀ σ' : TState C _, σ'.erase = τ' → σ.H <+: σ'.H → holds σ' φ)
        (U.apply σ.erase)
      revert hrel H₀
      cases U.apply σ.erase with
      | error e =>
        cases Solidity.Upd.apply (U.erase ns) τ with
        | error _ => intro _ H₀; exact H₀
        | ok _ => intro hrel; exact hrel.elim
      | ok σ₁ =>
        cases hτ : Solidity.Upd.apply (U.erase ns) τ with
        | error _ => intro hrel; exact hrel.elim
        | ok τ₁ =>
          intro hrel _ σ' e _
          subst e
          refine ih h₁ hrel fun ρ hρ => ?_
          let ρ₀ := mergeOn B τ ρ
          have hfr := Solidity.Upd.apply_frame (mergeOn_agree B τ ρ) (U.erase ns) hav
          have Hρ₀ := erase_upd_holds.1 (H ρ₀ (mergeOn_agree B τ ρ))
          rw [hτ] at hfr
          revert hfr Hρ₀
          cases hρ₁ : Solidity.Upd.apply (U.erase ns) ρ₀ with
          | error _ => intro hfr; exact hfr.elim
          | ok ρ₁ =>
            intro hfr Hρ₁
            refine holds_of_envAgree_nil ?_ Hρ₁
            have h₁ρ := Solidity.Semantics.EnvAgreeExcept.trans (envAgree_symm hfr) hρ
            refine ⟨h₁ρ.storage, h₁ρ.heap, h₁ρ.nextId, h₁ρ.net, fun y _ => ?_, h₁ρ.selfBalance,
              h₁ρ.tx⟩
            by_cases hy : y ∈ B
            · rw [Solidity.Upd.foldl_lookup (U.erase ns) (fun hv => hav y hv hy) hρ₁]
              exact lookupBy_mergeOn hy
            · exact h₁ρ.env y hy
    · cases h
  | havoc φ ih =>
    intro ns B h σ τ hag H
    change φ.posB ns = some B at h
    intro st nt
    have e : τ.havoc st.erase nt = withLocals (σ.erase.glob.havoc st.erase nt) τ.env := by
      have hw := hag.wl
      generalize τ.env = env at hw ⊢
      subst hw; rfl
    have hag' := hag.withGlob (σ.erase.glob.havoc st.erase nt)
    rw [← e, ← TState.havoc_erase] at hag'
    refine ih h hag' fun ρ hρ => ?_
    refine holds_of_envAgree_nil ?_ (H (mergeOn B τ ρ) (mergeOn_agree B τ ρ) st.erase nt)
    refine ⟨hρ.storage, hρ.heap, hρ.nextId, hρ.net, fun y _ => ?_, hρ.selfBalance, hρ.tx⟩
    by_cases hy : y ∈ B
    · exact lookupBy_mergeOn hy
    · exact ((mergeOn_agree B τ ρ).env y hy).symm.trans (hρ.env y hy)
  | all x p φ ih =>
    intro ns B h σ τ hag H
    have hx : ns.contains x = false := by
      cases hn : ns.contains x
      · rfl
      · simp only [Fml.posB, hn, if_true] at h; cases h
    change (if ns.contains x then none
      else (φ.posB (x :: ns)).bind fun B => if B.contains x then none else some B) = some B at h
    rw [if_neg (by simp only [hx]; decide)] at h
    obtain ⟨B', h₁, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · cases h
    · cases h
      rename_i hxB
      have hxn : x ∉ ns := fun hm => by simp only [List.contains_iff_mem.2 hm] at hx; cases hx
      have hxB' : x ∉ B := fun hm => hxB (List.contains_iff_mem.2 hm)
      intro w
      refine ih h₁ (σ := σ.push (t := .val p) w) (hag.push (t := .val p) hxn (PrimTy.erase w))
        fun ρ hρ => ?_
      refine holds_of_envAgree_nil ?_
        (H (mergeOn B τ ρ) (mergeOn_agree B τ ρ) (PrimTy.erase w) (PrimTy.admits_erase w))
      refine ⟨hρ.storage, hρ.heap, hρ.nextId, hρ.net, fun y _ => ?_, hρ.selfBalance, hρ.tx⟩
      by_cases hy : y ∈ B
      · have hyx : y ≠ x := fun e => hxB' (e ▸ hy)
        simp only [Semantics.State.setEnv, SemanticsProperties.lookupBy_setBy_ne hyx]
        exact lookupBy_mergeOn hy
      · rw [← hρ.env y hy]
        by_cases hyx : y = x
        · subst hyx
          simp only [Semantics.State.setEnv, SemanticsProperties.lookupBy_setBy_self]
          rfl
        · simp only [Semantics.State.setEnv, SemanticsProperties.lookupBy_setBy_ne hyx]
          exact ((mergeOn_agree B τ ρ).env y hy).symm
  | bind m x t φ ih =>
    intro ns B h σ τ hag H
    have hx : ns.contains x = false := by
      cases hn : ns.contains x
      · rfl
      · simp only [Fml.posB, hn, if_true] at h; cases h
    change (if ns.contains x then none else (φ.posB (x :: ns)).map (x :: ·)) = some B at h
    rw [if_neg (by simp only [hx]; decide)] at h
    obtain ⟨B', h₁, rfl⟩ := Option.map_eq_some_iff.1 h
    have hxn : x ∉ ns := fun hm => by simp only [List.contains_iff_mem.2 hm] at hx; cases hx
    refine Modality.forallB_intro fun v => ?_
    refine ih h₁ (σ := σ.push v) (hag.push hxn (LTy.TDenote.erase t v)) fun ρ hρ => H ρ ?_
    exact Solidity.Semantics.EnvAgreeExcept.trans
      ((Solidity.Semantics.EnvAgreeExcept.refl _ τ).setEnv_right List.mem_cons_self _)
      (Solidity.Semantics.EnvAgreeExcept.of_sub (fun _ hy => List.mem_cons_of_mem _ hy) hρ)

/-- The empty context agrees with the global part alone. -/
theorem Agree.nil (σ : State C []) : Agree [] σ (withLocals σ.glob []) where
  len := rfl
  nodup := List.nodup_nil
  glob := rfl
  env _ hm := nomatch hm

/-- **A leaf is valid when its erasure is**, its hidden binders where
`Fml.posB` takes them. -/
theorem Valid.of_erase {φ : Fml C []} (hp : (φ.posB []).isSome = true)
    (h : Solidity.Valid (φ.erase [])) : Valid φ := by
  intro σ
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 hp
  exact holds_of_erase_pos φ hB (Agree.nil σ.erase) fun ρ _ => h ρ

end Solidity.Core
