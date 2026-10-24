import Solidity.Calculus.RewritePast
import Solidity.Calculus.LeafDerive
import Solidity.Calculus.TermSize

/-!
# A rigid branch condition before its context

`applyOnRigidFormula` substitutes only the condition through local updates.
A successful sibling derivation supplies the original context, including
diamond landing and exhaustion obligations; the projection alone cannot
close an arbitrary diamond sequent. A refused rigid projection keeps both branches; non-ground conditions use
the ordinary bounded closer.
-/

open Solidity
namespace Solidity.Hyps

/-- A per-step syntax cap: both the condition and update fit before
substitution, preventing repeated assignments from expanding exponentially. -/
def rigidSize : Nat := 512

/-- `rigid` compiled by matching on the context. -/
def rigidM {C : Contract} : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (Fml C [])
  | _, .nil, c => bif decide (c.tmSize ≤ rigidSize) then some c else none
  | _, .pre H _, c => rigidM H c
  | _, .upd H _ U, c =>
      bif decide (c.tmSize ≤ rigidSize) && decide (U.tmSize ≤ rigidSize) then
        Fml.substU U c >>= rigidM H
      else none
  | _, .all H _ _, c | _, .bind H _ _ _, c =>
      Fml.thinFO? (.drop .refl) c >>= rigidM H
  | _, _, _ => none


/-- The condition read before the context's updates; a binder may be
dropped only when the condition does not read it. By the recursor. -/
@[implemented_by rigidM]
def rigid {C : Contract} {Γ : Ctx} (H : Hyps C [] Γ) : Fml C Γ → Option (Fml C []) :=
  Hyps.rec (motive := fun Γ _ => Fml C Γ → Option (Fml C []))
    (fun c => bif decide (c.tmSize ≤ rigidSize) then some c else none)
    (fun _ _ ih c => ih c)
    (fun _ _ U ih c =>
      bif decide (c.tmSize ≤ rigidSize) && decide (U.tmSize ≤ rigidSize) then
        Fml.substU U c >>= ih
      else none)
    (fun _ _ _ => none)
    (fun _ _ _ ih c => Fml.thinFO? (.drop .refl) c >>= ih)
    (fun _ _ _ _ ih c => Fml.thinFO? (.drop .refl) c >>= ih)
    (fun _ _ _ _ => none)
    (fun _ _ _ _ _ => none)
    (fun _ _ _ => none) H

theorem rigid_eq_rigidM {C : Contract} {Γ : Ctx} (H : Hyps C [] Γ) (c : Fml C Γ) :
    H.rigid c = H.rigidM c := by
  induction H with
  | nil | havoc | anon | allocAll | grow => rfl
  | pre H a ih => exact ih c
  | upd H m U ih =>
    change (cond _ (Fml.substU U c >>= H.rigid) none) =
      (cond _ (Fml.substU U c >>= H.rigidM) none)
    exact congrArg (fun f => cond _ (Fml.substU U c >>= f) none) (funext ih)
  | all H x p ih | bind H m x t ih =>
    change (Fml.thinFO? (.drop .refl) c >>= H.rigid) =
      (Fml.thinFO? (.drop .refl) c >>= H.rigidM)
    exact congrArg (fun f => Fml.thinFO? (.drop .refl) c >>= f) (funext ih)

/-- The projected condition can strengthen a sequent only while preserving
the original context's landing obligations. -/
theorem rigid_lift {C : Contract} {Γ : Ctx} (H : Hyps C [] Γ) :
    ∀ (c : Fml C Γ) {c₀ : Fml C []}, rigid H c = some c₀ → Fml.Valid c₀ →
      ∀ {φ ψ : Fml C Γ}, (∀ τ, holds τ c → holds τ φ → holds τ ψ) →
        ∀ σ, holds σ (H.wrap φ) → holds σ (H.wrap ψ) := by
  induction H with
  | nil =>
    intro c c₀ he hc φ ψ h σ hp
    change (cond _ (some c) none) = some c₀ at he
    cases hf : decide (c.tmSize ≤ rigidSize)
    · rw [hf, cond_false] at he; cases he
    · rw [hf, cond_true] at he
      cases he; exact h σ (hc σ) hp
  | pre H a ih =>
    intro c c₀ he hc φ ψ h
    exact ih c he hc (φ := .imp a φ) (ψ := .imp a ψ)
      (fun τ hτ hp ha => h τ hτ (hp ha))
  | upd H m U ih =>
    intro c c₀ he hc φ ψ h
    change (cond _ (Fml.substU U c >>= H.rigid) none) = some c₀ at he
    cases hf : decide (c.tmSize ≤ rigidSize) && decide (U.tmSize ≤ rigidSize)
    · rw [hf, cond_false] at he; cases he
    · rw [hf, cond_true] at he
      obtain ⟨c', hs, he⟩ := Option.bind_eq_some_iff.1 he
      apply ih c' he hc (φ := .upd m U φ) (ψ := .upd m U ψ)
      intro τ hτ hp
      exact Upd.afterT_introX (fun he => hp.of_none he) fun _ σ' hl =>
        h σ' ((Fml.substU_holds hl c hs).1 hτ) (hp.of_lands hl)
  | all H x p ih =>
    intro c c₀ he hc φ ψ h
    obtain ⟨c', hs, he⟩ := Option.bind_eq_some_iff.1 he
    apply ih c' he hc (φ := .all x p φ) (ψ := .all x p ψ)
    intro τ hτ hp v
    exact h (τ.push v) ((Fml.thinFO?_holds (.drop .refl) c hs (τ.push v)).1 hτ) (hp v)
  | bind H m x t ih =>
    intro c c₀ he hc φ ψ h
    obtain ⟨c', hs, he⟩ := Option.bind_eq_some_iff.1 he
    apply ih c' he hc (φ := .bind m x t φ) (ψ := .bind m x t ψ)
    intro τ hτ hp v
    exact h (τ.push v) ((Fml.thinFO?_holds (.drop .refl) c hs (τ.push v)).1 hτ) (hp v)
  | havoc H ih | anon H xs ih | grow H ih | allocAll H x A ih =>
    intro c c₀ he
    cases he
end Solidity.Hyps

namespace Solidity.Seq

open Decide

/-- Try rigid substitution first on literal-local conditions. A failed
rigid check or refused projection leaves both branches; non-ground conditions
use `refuteS`. -/
def refuteLanded {C : Contract} {Γ : Ctx} (H : Hyps C [] Γ) (c : Fml C Γ) : Bool :=
  bif H.groundS c then
    match H.rigid (.not c) with
    | some q => ((H.pre c).wrap .ff).modalFree && (checkCore q).getD false
    | none => false
  else refuteS H c

/-- A refuted branch, using a sibling derivation to retain successful
execution of the shared prefix even under the diamond. -/
theorem refuteLanded_sound {C : Contract} {R : RuleSet} {Γ : Ctx}
    (H : Hyps C [] Γ) (c : Fml C Γ) (h : refuteLanded H c = true)
    {a φ : Fml C Γ} (live : Proves C R [] (H.pre a) φ) : Proves C R [] (H.pre c) .ff := by
  unfold refuteLanded at h
  cases hg : H.groundS c
  · rw [hg, cond_false] at h
    exact refuteS_sound H c h
  · rw [hg, cond_true] at h
    cases hr : H.rigid (.not c) with
    | none =>
      rw [hr] at h
      cases h
    | some q =>
      rw [hr, Bool.and_eq_true] at h
      have hq : checkCore q = some true := by
        cases he : checkCore q with
        | none => simp only [he, Option.getD_none, Bool.false_eq_true, and_false] at h
        | some b => exact congrArg some (show b = true by simpa only [he, Option.getD_some] using h.2)
      exact Proves.closeHolds (fun σ =>
        H.rigid_lift (.not c) hr (checkCore_valid hq)
          (φ := .imp a φ) (ψ := .imp c .ff)
          (fun _ hn _ hc => False.elim (hn hc)) σ (live.sound σ)) h.1

end Solidity.Seq
