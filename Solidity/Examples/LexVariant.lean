import Solidity.Calculus.LexVariantSound
import Solidity.Examples.LexMetrics

/-!
# Lexicographic VC helper regressions

The comparison admits a reset in a later component, rejects equality and
increase, and snapshots reject an undefined later component even when the
first component has decreased. The source phase loop's exact metrics also
have successful typed snapshot landings. Rule-table integration is separate.
-/
namespace Solidity.Examples.LexVariant

open LoopLex

private def zero : PrimTy.uint.Denote := PrimTy.ofLit .uint 0 (by decide)
private def one : PrimTy.uint.Denote := PrimTy.ofLit .uint 1 (by decide)
private def two : PrimTy.uint.Denote := PrimTy.ofLit .uint 2 (by decide)
private def three : PrimTy.uint.Denote := PrimTy.ofLit .uint 3 (by decide)

private def before : UIntTuple 2 := (two, zero, ())
private def reset : UIntTuple 2 := (one, three, ())
private def increase : UIntTuple 2 := (three, zero, ())

theorem reset_decreases (σ : State C Γ) :
    holds (saveState (saveState σ before) reset) (snapshotsDecrease 2) :=
  (snapshotsDecrease_holds σ before reset).2 (by decide)

theorem equal_rejected (σ : State C Γ) :
    ¬ holds (saveState (saveState σ before) before) (snapshotsDecrease 2) := by
  rw [snapshotsDecrease_holds]
  decide

theorem increase_rejected (σ : State C Γ) :
    ¬ holds (saveState (saveState σ before) increase) (snapshotsDecrease 2) := by
  rw [snapshotsDecrease_holds]
  decide

private def undefinedTail : LoopMetrics C Γ 3 :=
  .cons (.simple (.lit 1 (by decide)))
    (.cons (.simple (.lit 0 (by decide)))
      (.cons (.binop .div rfl rfl (.simple (.lit 1 (by decide)))
        (.simple (.lit 0 (by decide)))) .nil))

/-- The final component is evaluated even though the new first component 1
would be smaller than the old first component 2. -/
theorem undefined_later_rejected (σ : State C Γ) (k : Nat) :
    (snapshot k undefinedTail).globT σ = none :=
  snapshot_fails_of_undefined σ k undefinedTail (e := .revert) rfl

theorem undefined_later_no_landing (σ : State C Γ) (k : Nat)
    (g : GlobT C σ.H) (τ : State C (SavedCtx 3 Γ)) :
    ¬ (snapshot k undefinedTail).Lands σ g τ := by
  intro h
  have hg := h.1
  rw [undefined_later_rejected] at hg
  cases hg

/-- Existing source phase-loop metrics pass the full snapshot evaluator. -/
theorem source_metrics_land (σ : State Examples.Termination.Flags Examples.Termination.FlagCtx)
    (k : Nat) : ∃ xs,
    (snapshot k Examples.LexMetrics.metrics).Lands σ σ.globG (saveState σ xs) ∧
      xs.toNat = Examples.LexMetrics.phaseValues σ := by
  obtain ⟨xs, hx, heq⟩ := readMetrics_of_eval σ Examples.LexMetrics.metrics
    (Examples.LexMetrics.metrics_eval σ)
  exact ⟨xs, snapshot_lands σ k _ xs hx, heq⟩

/-- Capturing ghost metrics preserves the original variables in their scope. -/
theorem source_metrics_survive_capture
    (σ : State Examples.Termination.Flags Examples.Termination.FlagCtx) :
    LoopMetrics.eval (saveState σ reset)
      (Examples.LexMetrics.metrics.wk (.ofExt (savedExt _ 2))) =
        .ok (Examples.LexMetrics.phaseValues σ) := by
  rw [metrics_eval_saved, Examples.LexMetrics.metrics_eval]

end Solidity.Examples.LexVariant
