import Solidity.Calculus.Core.TLogic
import Solidity.Calculus.Core.CloseErase

/-!
# A goal closed by its erasure's validity, over the typed state

`tholds_of_erase_valid`: `Calculus/Core/CloseErase.lean`'s
`holds_of_erase_valid` read over the typed state, the same induction with
the untyped states agreeing with the typed state's erasure
(`TState.erase`), for `Fml.TClosable` leaves (`Calculus/Core/Closable.lean`):
an update in a positive position may be a diamond, since the typed reading
of an update asks only of the typed states that erase to the one it ends in
(`tholds`), not the `State.BoolOK` M3's diamond asks.  Its atoms go through
M3's reading: a first-order formula (`Fml.FO`) reads the same on both
(`tholds_iff_holds`), and a leaf (`Fml.Leaf`) holds over the typed state
where it holds over its erasure (`tholds_of_holds`).  `Proves.close`
(`Calculus/Core/Proves.lean`) is this, behind a context.
-/

namespace Solidity.Core

open Solidity (Modality Avoids)

variable {C : Contract}

/-! ## The typed state erased -/

theorem _root_.Solidity.PrimTy.admits_erase : {p : PrimTy} → (v : p.Denote) → p.admits (PrimTy.erase v)
  | .bool, _ => trivial
  | .uint, ⟨_, h⟩ => by
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    exact h
  | .int, ⟨_, h⟩ => by
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    exact h

theorem _root_.Solidity.PrimTy.exists_of_admits :
    {p : PrimTy} → {v : Semantics.Value} → p.admits v → ∃ w : p.Denote, PrimTy.erase w = v
  | .bool, .bool b, _ => ⟨b, rfl⟩
  | .uint, .int n, h =>
    ⟨(⟨n, by simp only [PrimTy.inRange, decide_eq_true_eq]; exact h⟩ :
      {n : Int // PrimTy.uint.inRange n = true}), rfl⟩
  | .int, .int n, h =>
    ⟨(⟨n, by
        simp only [PrimTy.inRange, decide_eq_true_eq]
        exact h⟩ :
      {n : Int // PrimTy.int.inRange n = true}), rfl⟩
  | .bool, .int _, h | .uint, .bool _, h | .int, .bool _, h => h.elim

theorem LTy.boolOK_erase {H : HTy} : (t : LTy) → (v : t.TDenote C H) →
    LTy.BoolOK (C := C) t (LTy.TDenote.erase t v)
  | .val .bool, v => ⟨v, rfl⟩
  | .val .uint, _ | .val .int, _ | .alias _, _ | .mem _, _ | .old, _ | .oldNet, _ => trivial

theorem TEnv.erase_boolOK {H : HTy} : (Γ : Ctx) → (e : TEnv C H Γ) →
    Env.All (LTy.BoolOK (C := C)) (TEnv.erase Γ e)
  | [], _ => trivial
  | t :: Γ, e => ⟨LTy.boolOK_erase t e.1, TEnv.erase_boolOK Γ e.2⟩

/-- A typed state's `bool` locals hold `bool`s. -/
theorem TState.erase_boolOK {Γ : Ctx} (σ : TState C Γ) : σ.erase.BoolOK :=
  TEnv.erase_boolOK Γ σ.env

theorem TState.havoc_erase {Γ : Ctx} (σ : TState C Γ) (st : Storage C) (nt : List (Int × Int)) :
    (σ.havoc st nt).erase = σ.erase.withGlob (σ.erase.glob.havoc st.erase nt) := rfl

theorem TState.anon_erase {Γ : Ctx} (σ : TState C Γ) (xs : List ((t : LTy) × Idx Γ t))
    (b : (x : (t : LTy) × Idx Γ t) → x.1.TDenote C σ.H) :
    (σ.anon xs b).erase = σ.erase.anon xs fun x => LTy.TDenote.erase x.1 (b x) := by
  have key : ∀ (ys : List ((t : LTy) × Idx Γ t)) (e : TEnv C σ.H Γ),
      (σ.withEnv (ys.foldl (fun e x => TEnv.set x.2 (b x) e) e)).erase =
        ys.foldl (fun τ x => τ.setLocal x.2 (LTy.TDenote.erase x.1 (b x))) (σ.withEnv e).erase := by
    intro ys
    induction ys with
    | nil => intro e; rfl
    | cons x ys ih =>
      intro e
      rw [List.foldl_cons, List.foldl_cons, ih]
      exact congrArg (fun τ => List.foldl _ τ ys) (TState.setLocal_erase (σ.withEnv e) x.2 (b x))
  exact key xs σ.env

/-! ## Typed and erased readings -/

theorem _root_.Solidity.Modality.afterC_imp {α : Type} {m : Modality} {p q : α → Prop}
    {r : Semantics.Res α} (h : m.afterC p r) (hpq : ∀ a, p a → q a) : m.afterC q r := by
  cases r with
  | ok a => exact hpq a h
  | error _ => exact h

/-- **A first-order formula reads the same** over a typed state and its
erasure. -/
theorem tholds_iff_holds : {Γ : Ctx} → (φ : Fml C Γ) → φ.FO = true → (σ : TState C Γ) →
    (tholds σ φ ↔ holds σ.erase φ)
  | _, .tt, _, _ => Iff.rfl
  | _, .eq _ _, _, _ => Iff.rfl
  | _, .defined _, _, _ => Iff.rfl
  | _, .not φ, h, σ => not_congr (tholds_iff_holds φ h σ)
  | _, .and φ ψ, h, σ => by
    have h' : φ.FO = true ∧ ψ.FO = true := Bool.and_eq_true_iff.mp h
    exact and_congr (tholds_iff_holds φ h'.1 σ) (tholds_iff_holds ψ h'.2 σ)
  | _, .imp φ ψ, h, σ => by
    have h' : φ.FO = true ∧ ψ.FO = true := Bool.and_eq_true_iff.mp h
    exact imp_congr (tholds_iff_holds φ h'.1 σ) (tholds_iff_holds ψ h'.2 σ)
  | _, .all _ p φ, h, σ => by
    show (∀ v : p.Denote, tholds (σ.push (t := .val p) v) φ) ↔
      ∀ v, p.admits v → holds (σ.erase.push (t := .val p) v) φ
    constructor
    · intro hv v ha
      obtain ⟨w, rfl⟩ := PrimTy.exists_of_admits ha
      exact (tholds_iff_holds φ h (σ.push (t := .val p) w)).1 (hv w)
    · intro hv w
      exact (tholds_iff_holds φ h (σ.push (t := .val p) w)).2 (hv _ (PrimTy.admits_erase w))
  | _, .upd .., h, _ | _, .modal .., h, _ | _, .havoc _, h, _ | _, .bind .., h, _
  | _, .anon .., h, _ => nomatch h

/-- **A leaf that holds over the erasure holds over the typed state.** -/
theorem tholds_of_holds : {Γ : Ctx} → (φ : Fml C Γ) → φ.Leaf = true → (σ : TState C Γ) →
    holds σ.erase φ → tholds σ φ
  | _, .tt, _, _, h => h
  | _, .eq _ _, _, _, h => h
  | _, .defined _, _, _, h => h
  | _, .not φ, hl, σ, h => fun hφ => h ((tholds_iff_holds φ hl σ).1 hφ)
  | _, .and φ ψ, hl, σ, h => by
    have hl' : φ.Leaf = true ∧ ψ.Leaf = true := Bool.and_eq_true_iff.mp hl
    exact ⟨tholds_of_holds φ hl'.1 σ h.1, tholds_of_holds ψ hl'.2 σ h.2⟩
  | _, .imp φ ψ, hl, σ, h => by
    have hl' : φ.FO = true ∧ ψ.Leaf = true := Bool.and_eq_true_iff.mp hl
    exact fun hφ => tholds_of_holds ψ hl'.2 σ (h ((tholds_iff_holds φ hl'.1 σ).1 hφ))
  | _, .upd m U φ, hl, σ, h => by
    have h' := (Modality.afterT_iff.1 h) fun _ => σ.erase_boolOK
    show m.afterC (fun τ => ∀ σ' : TState C _, σ'.erase = τ → tholds σ' φ) (U.apply σ.erase)
    refine Modality.afterC_imp h' fun τ hτ σ' e => ?_
    subst e
    refine tholds_of_holds φ hl σ' ?_
    cases m with
    | box => exact hτ
    | diamond => exact hτ.2
  | _, .modal .., hl, _, _ => nomatch hl
  | _, .havoc φ, hl, σ, h => fun st nt => by
    refine tholds_of_holds φ hl (σ.havoc st nt) ?_
    rw [TState.havoc_erase]
    exact h st.erase nt
  | _, .all _ p φ, hl, σ, h => fun w =>
    tholds_of_holds φ hl (σ.push (t := .val p) w) (h _ (PrimTy.admits_erase w))
  | _, .bind _ t φ, hl, σ, h => fun v => tholds_of_holds φ hl (σ.push v) (h _)
  | _, .anon xs φ, hl, σ, h => fun b => by
    refine tholds_of_holds φ hl (σ.anon xs b) ?_
    rw [TState.anon_erase]
    exact h _

/-! ## A leaf closed by its erasure's validity

`holds_of_erase_valid`'s induction, read over the typed state: the same
untyped states, now agreeing with the typed state's erasure.  An update may
be a diamond (`Fml.TClosable`): the erasure's diamond gives the run, and the
typed reading asks only of the typed states that erase to the one it ends
in. -/

open Semantics (lookupBy setBy EnvAgreeExcept) in
theorem tholds_of_erase_valid_agree : {Γ : Ctx} → (φ : Fml C Γ) → {ns : List Var} →
    φ.TClosable ns → Avoids φ.bindNames ns → {σ : TState C Γ} → {τ₀ : Semantics.State} →
    Agree ns σ.erase τ₀ →
    (∀ τ, EnvAgreeExcept φ.bindNames τ τ₀ → Solidity.holds τ (φ.erase ns)) → tholds σ φ
  | _, .tt, _, _, _, _, _, _, _ => trivial
  | _, .eq a b, _, _, _, σ, τ₀, hag, h =>
    tholds_of_holds (.eq a b) rfl σ
      ((holds_erase (.eq a b) trivial hag).2 (h τ₀ (agreeExcept_refl _ τ₀)))
  | _, .defined t, _, _, _, σ, τ₀, hag, h =>
    tholds_of_holds (.defined t) rfl σ
      ((holds_erase (.defined t) trivial hag).2 (h τ₀ (agreeExcept_refl _ τ₀)))
  | _, .not φ, _, hφ, _, σ, τ₀, hag, h =>
    tholds_of_holds (.not φ) hφ.2 σ
      ((holds_erase (.not φ) hφ.1 hag).2 (h τ₀ (agreeExcept_refl _ τ₀)))
  | _, .modal .., _, hφ, _, _, _, _, _ => hφ.elim
  | _, .and φ ψ, _, hφ, hB, _, _, hag, h =>
    ⟨tholds_of_erase_valid_agree φ hφ.1 (Avoids.left hB) hag fun τ hτ =>
        (h τ (agreeExcept_mono hτ fun _ hy => List.mem_append_left _ hy)).1,
      tholds_of_erase_valid_agree ψ hφ.2 (Avoids.right hB) hag fun τ hτ =>
        (h τ (agreeExcept_mono hτ fun _ hy => List.mem_append_right _ hy)).2⟩
  | _, .imp φ ψ, _, hφ, hB, σ, _, hag, h => fun ha =>
    tholds_of_erase_valid_agree ψ hφ.2 hB hag fun τ hτ =>
      h τ hτ ((holds_erase φ hφ.1.1 (hag.congrExcept hτ hB)).1
        ((tholds_iff_holds φ hφ.1.2 σ).1 ha))
  | _, .upd m U φ, ns, hφ, _, σ, τ₀, hag, h => by
    obtain ⟨hU, hUB, hBU, hφ⟩ := hφ
    have hE : ∀ τ, EnvAgreeExcept φ.bindNames τ τ₀ →
        Solidity.holds τ (.upd m (U.erase ns) (φ.erase (U.names ns))) := fun τ hτ => by
      have h' := h τ hτ
      simp only [Fml.erase] at h'
      split at h'
      · rename_i hnil
        rw [hnil]
        exact h'
      · exact h'
    have hR := Upd.apply_erase hag U hU
    show m.afterC (fun τ => ∀ σ' : TState C _, σ'.erase = τ → tholds σ' φ) (U.apply σ.erase)
    cases hσ : U.apply σ.erase with
    | error =>
      rw [hσ] at hR
      cases m with
      | box => trivial
      | diamond =>
        have h1 : Modality.after .diamond (Solidity.holds · (φ.erase (U.names ns)))
            (Solidity.Upd.apply (U.erase ns) τ₀) := hE τ₀ (agreeExcept_refl _ τ₀)
        revert h1 hR
        cases Solidity.Upd.apply (U.erase ns) τ₀ with
        | error => intro _ h1; exact h1.elim
        | ok _ => intro hR _; exact hR.elim
    | ok σ'' =>
      rw [hσ] at hR
      cases hτ₀ : Solidity.Upd.apply (U.erase ns) τ₀ with
      | error => rw [hτ₀] at hR; exact hR.elim
      | ok τ₀' =>
        rw [hτ₀] at hR
        intro σ' e
        subst e
        refine tholds_of_erase_valid_agree φ hφ hBU hR fun τ' hτ' => ?_
        have h1 : Modality.after m (Solidity.holds · (φ.erase (U.names ns)))
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
    have hag' := hag.withGlob (σ.erase.glob.havoc st.erase nt)
    have e : withLocals (σ.erase.glob.havoc st.erase nt) τ₀.env = τ₀.havoc st.erase nt := by
      have hw := hag.wl
      generalize τ₀.env = env at hw ⊢
      subst hw
      rfl
    rw [e] at hag'
    refine tholds_of_erase_valid_agree φ hφ hB (σ := σ.havoc st nt) hag' fun τ' hτ' => ?_
    have h1 := h (overlay φ.bindNames τ' τ₀) (agreeExcept_overlay _ _ _) st.erase nt
    refine (holds_congr_full (agreeExcept_full (agreeExcept_trans
      ((agreeExcept_overlay _ τ' τ₀).havoc st.erase nt) (agreeExcept_symm hτ')) fun y hy => ?_) _).1 h1
    show lookupBy y (overlay _ τ' τ₀).env = _
    rw [lookupBy_overlay, if_pos hy]
  | _, .all x p φ, _, hφ, hB, σ, τ₀, hag, h => fun v => by
    obtain ⟨hx, hxB, hφ⟩ := hφ
    refine tholds_of_erase_valid_agree φ hφ (fun y hy hm => ?_) (σ := σ.push (t := .val p) v)
      (hag.push (t := .val p) hx (PrimTy.erase v)) fun τ' hτ' => ?_
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact hxB hy
      · exact hB y hy hm
    · have h1 := h (overlay φ.bindNames τ' τ₀) (agreeExcept_overlay _ _ _) (PrimTy.erase v)
        (PrimTy.admits_erase v)
      refine (holds_congr_full (agreeExcept_full (agreeExcept_trans
        ((agreeExcept_overlay _ τ' τ₀).setEnv_both x _) (agreeExcept_symm hτ')) fun y hy => ?_) _).1 h1
      have hne : y ≠ x := fun e => by subst e; exact hxB hy
      show lookupBy y (setBy x _ (overlay _ τ' τ₀).env) = _
      rw [SemanticsProperties.lookupBy_setBy_ne hne, lookupBy_overlay, if_pos hy]
  | _, .bind x t φ, _, hφ, hB, σ, τ₀, hag, h => fun v => by
    obtain ⟨hx, hxB, hφ⟩ := hφ
    refine tholds_of_erase_valid_agree φ hφ (fun y hy hm => ?_) (σ := σ.push v)
      (hag.push hx (LTy.TDenote.erase t v)) fun τ' hτ' => ?_
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact hxB hy
      · exact hB y (List.mem_cons_of_mem _ hy) hm
    · exact h τ' (agreeExcept_trans (agreeExcept_mono hτ' fun _ hy => List.mem_cons_of_mem _ hy)
        (agreeExcept_mono (agreeExcept_setEnv τ₀ x _) fun _ hy => by
          rw [List.mem_singleton.1 hy]; exact List.mem_cons_self))
  | _, .anon xs φ, ns, hφ, hB, σ, τ₀, hag, h => fun b => by
    obtain ⟨τ₁, h₁, h₂⟩ := Agree.anon (fun x => LTy.TDenote.erase x.1 (b x)) xs hag
    have hag' : Agree ns (σ.anon xs b).erase (overlay (xs.map fun x => x.2.name ns) τ₁ τ₀) := by
      rw [TState.anon_erase]
      refine h₁.congrEnv ?_ fun y => ?_
      · rw [State.glob_anon _ xs σ.erase]
        have hw := hag.wl
        generalize τ₀.env = env at hw ⊢
        subst hw
        rfl
      · rw [lookupBy_overlay]
        split
        · rfl
        · exact (h₂ y ‹_›).symm
    refine tholds_of_erase_valid_agree φ hφ hB hag' fun τ' hτ' => ?_
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

/-- **A leaf closed by its erasure's validity**, over the typed state, a
diamond update in a positive position allowed (`Fml.TClosable`). -/
theorem tholds_of_erase_valid {Γ : Ctx} (φ : Fml C Γ) {ns : List Var} (hlen : ns.length = Γ.length)
    (hnd : ns.Nodup) (hc : φ.TClosable ns) (hB : Avoids φ.bindNames ns)
    (h : Solidity.Valid (φ.erase ns)) (σ : TState C Γ) : tholds σ φ :=
  tholds_of_erase_valid_agree φ hc hB (Agree.erase σ.erase hnd hlen) fun τ _ => h τ

end Solidity.Core
