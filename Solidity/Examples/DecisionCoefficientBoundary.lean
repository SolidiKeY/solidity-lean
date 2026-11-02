import Solidity.Calculus.DecisionCoefficientBoundary
import Solidity.Calculus.Notation
import Solidity.Examples.DecisionMemoryParameterData

/-!
# Inhabited controls for the source-coefficient boundary

These controls keep coverage, source admission and semantic verdicts separate.
The folded coefficient is the same source shape as the retained VA1 counterexample.
No general program-free inclusion or arbitrary-coefficient decision is claimed.
-/
namespace Solidity.Examples.DecisionCoefficientBoundary
open Solidity.Decide Solidity.Decide.CoefficientBoundary
set_option Elab.async false

def Bank : Contract := contract!{ uint value; }
local instance coefficientBoundaryContract : InContract := ⟨Bank⟩

/-- A direct coefficient with the same double on both sides. -/
def directTwo : Fml Bank [] := dl[Bank]{ ∀ uint x; 2 * x = x + x }
/-- A direct coefficient whose equation fails at one. -/
def directThree : Fml Bank [] := dl[Bank]{ ∀ uint x; 3 * x = x + x }
/-- Source folding admits coverage while direct source admission rejects the product. -/
def foldedTwo : Fml Bank [] := dl[Bank]{ ∀ uint x; (1 + 1) * x = x + x }

/-- Exact membership of the positive control in the supported family. -/
theorem directTwo_family : directTwo = coefficientLeaf (.app0 (.lit (uintOfNat 2))) := rfl
/-- Exact membership of the refuted control in the supported family. -/
theorem directThree_family : directThree = coefficientLeaf (.app0 (.lit (uintOfNat 3))) := rfl
/-- The nonliteral coefficient stays within the family, on its rejected side. -/
theorem foldedTwo_family : foldedTwo = coefficientLeaf
    (.app2 (.binop .add rfl) (.app0 (.lit (uintOfNat 1))) (.app0 (.lit (uintOfNat 1)))) := rfl

/-- Observe all three properties without specializing the decision pipeline to a closed fixture. -/
@[noinline] def observe {C : Contract} (φ : Fml C []) : Bool × Bool × String :=
  (φ.inTarget {}, φ.Covered, match decideGoal φ with
    | .proved => "proved"
    | .refuted _ => "refuted"
    | .unknown => "unknown")

/-- info: [(true, true, "proved"), (true, true, "refuted"), (false, true, "proved")] -/
#guard_msgs in #eval [directTwo, directThree, foldedTwo].map observe

/-- The positive direct-literal leaf is admitted by the frozen source predicate. -/
theorem directTwo_target : directTwo.inTarget {} = true := by decide +kernel
/-- Refutation does not remove the other direct-literal leaf from the target. -/
theorem directThree_target : directThree.inTarget {} = true := by decide +kernel
/-- The retained folded source shape remains rejected by source admission. -/
theorem foldedTwo_not_target : foldedTwo.inTarget {} = false := by decide +kernel
/-- The original complete pipeline recognizes the positive control. -/
theorem directTwo_covered : directTwo.Covered = true := by decide +kernel
/-- It also recognizes the false direct-literal equation. -/
theorem directThree_covered : directThree.Covered = true := by decide +kernel
/-- Folding yields coverage without repairing the original source shape. -/
theorem foldedTwo_covered : foldedTwo.Covered = true := by decide +kernel

private def provedCheck {C : Contract} : LeafVerdict C → Bool
  | .proved => true
  | _ => false
private def refutedCheck {C : Contract} : LeafVerdict C → Bool
  | .refuted _ => true
  | _ => false

private theorem proved_of_check {C : Contract} (φ : Fml C [])
    (h : provedCheck (decideGoal φ) = true) : decideGoal φ = .proved := by
  cases hd : decideGoal φ with
  | proved => rfl
  | refuted σ => rw [hd] at h; cases h
  | unknown => rw [hd] at h; cases h

private theorem refuted_of_check {C : Contract} (φ : Fml C [])
    (h : refutedCheck (decideGoal φ) = true) :
    ∃ σ : State C [], decideGoal φ = .refuted σ ∧ ¬ Fml.holdsH σ φ := by
  cases hd : decideGoal φ with
  | proved => rw [hd] at h; cases h
  | refuted σ => exact ⟨σ, rfl, decideGoal_refutes hd⟩
  | unknown => rw [hd] at h; cases h

/-- Exact public verdict, certified by kernel reduction of the actual decision. -/
theorem directTwo_proved : decideGoal directTwo = .proved :=
  proved_of_check directTwo (by decide +kernel)
/-- The positive control is valid under the unchanged existing hash premise. -/
theorem directTwo_validH : Fml.ValidH directTwo := decideGoal_sound directTwo_proved

/-- The negative control has an inhabited certified refuting state, with the exact premise. -/
theorem directThree_refuted :
    ∃ σ : State Bank [], decideGoal directThree = .refuted σ ∧ ¬ Fml.holdsH σ directThree :=
  refuted_of_check directThree (by decide +kernel)

/-- The rejected source shape is nevertheless proved by the existing decision pipeline. -/
theorem foldedTwo_proved : decideGoal foldedTwo = .proved :=
  proved_of_check foldedTwo (by decide +kernel)
/-- Its proof uses precisely the existing validity statement. -/
theorem foldedTwo_validH : Fml.ValidH foldedTwo := decideGoal_sound foldedTwo_proved

/-- The positive control has no hash, so its existing premise specializes to ordinary validity. -/
theorem directTwo_valid : Fml.Valid directTwo := by
  have hh : directTwo.hasHash = false := by decide +kernel
  exact (Fml.validH_iff hh).mp directTwo_validH

/-- The folded-source proof likewise specializes without adding a premise. -/
theorem foldedTwo_valid : Fml.Valid foldedTwo := by
  have hh : foldedTwo.hasHash = false := by decide +kernel
  exact (Fml.validH_iff hh).mp foldedTwo_validH

/-- The negative control realizes an ordinary countermodel, not only a failed source test. -/
theorem directThree_countermodel : ∃ σ : State Bank [], ¬ holds σ directThree := by
  have hh : directThree.hasHash = false := by decide +kernel
  obtain ⟨σ, _, hn⟩ := directThree_refuted
  exact ⟨σ, fun hv => hn ((Fml.holdsH_iff σ directThree hh).mpr hv)⟩

/-- A separately certified target/unknown control is outside the supported family by constructor shape. -/
theorem hiddenParameter_outside_family :
    ∀ c : Tm Solidity.Examples.Decision.Gaps [] (.val .uint),
      Solidity.Examples.Decision.memParamSame ≠ coefficientLeaf c := by
  intro c he
  cases he

end Solidity.Examples.DecisionCoefficientBoundary
