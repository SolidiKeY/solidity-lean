import Solidity.Calculus.DecisionNumericBounds
import Solidity.Examples.DecisionNumericFormula

/-!
# Source-bound controls
The raw size criterion is sufficient, not necessary. No budget or verdict
expectation is changed; actual classifications are reproduced before pins.
-/
namespace Solidity.Examples.DecisionNumericBounds
open Solidity.Decide
open Solidity.Examples.DecisionCoefficientBoundary (Bank)
set_option Elab.async false

def symbolicChain : Nat → Tm Bank [.val .uint] (.val .uint)
  | 0 => .pvV .here
  | n + 1 => .app2 (.binop .add rfl) (symbolicChain n) (.app0 (.lit (uintOfNat 0)))
def literalChain : Nat → Tm Bank [.val .uint] (.val .uint)
  | 0 => .app0 (.lit (uintOfNat 0))
  | n + 1 => .app2 (.binop .add rfl) (literalChain n) (.app0 (.lit (uintOfNat 0)))

theorem symbolicChain_grammar (n : Nat) : (symbolicChain n).UIntLinear := by
  induction n with
  | zero => exact .local .here
  | succ n ih => exact .add ih (.lit _)
theorem literalChain_grammar (n : Nat) : (literalChain n).UIntLinear := by
  induction n with
  | zero => exact .lit _
  | succ n ih => exact .add ih (.lit _)

def nearLimit : Fml Bank [] := primitivePrefixEq (.user "x") (symbolicChain 17) (symbolicChain 17)
def overRawBound : Fml Bank [] := primitivePrefixEq (.user "x") (symbolicChain 18) (symbolicChain 17)
def foldedLarge : Fml Bank [] := primitivePrefixEq (.user "unused") (literalChain 20) (literalChain 20)
def fails : Tm Bank [.val .uint] (.val .uint) := .app2 (.binop .sub rfl)
  (.app0 (.lit (uintOfNat 0))) (.app0 (.lit (uintOfNat 1)))
def bothFailed : Fml Bank [] := primitivePrefixEq (.user "unused") fails fails

@[noinline] def classify (φ : Fml Bank []) : Bool × Bool × Option Nat × String :=
  let covered := φ.Covered
  (φ.inTarget {}, covered, (leafOf? φ).map (fun ψ => ψ.stripAll.2.nodes),
    if covered then "covered: verdict search not profiled" else
      match decideGoal φ with | .proved => "proved" | .refuted _ => "refuted" | .unknown => "unknown")
/-- info: [(true, true, some 503, "covered: verdict search not profiled"), (true, false, some 517, "proved"),
  (true, true, some 27, "covered: verdict search not profiled"),
  (true, true, some 27, "covered: verdict search not profiled")] -/
#guard_msgs in #eval [nearLimit, overRawBound, foldedLarge, bothFailed].map classify

/-- info: (false, false, true, true) -/
#guard_msgs in #eval (overRawBound.hasHash, overRawBound.hashCovered,
  (dependentReduction? overRawBound).isSome, (quantReduction? overRawBound).isSome)

theorem nearLimit_source_size : (symbolicChain 17).size + (symbolicChain 17).size = 70 := by
  decide +kernel

theorem nearLimit_body_bound : ∃ ψ : LFml Bank,
    leafOf? nearLimit = some (.all 0 .uint ψ) ∧ ψ.nodes ≤ 511 :=
  uintPrefix_sourceBound_sufficient (.user "x") (symbolicChain_grammar 17) (symbolicChain_grammar 17)
    (by decide +kernel)

theorem nearLimit_body_nodes : (leafOf? nearLimit).map (fun ψ => ψ.stripAll.2.nodes) = some 503 := by
  decide +kernel

theorem nearLimit_target (w : Waivers) : nearLimit.inTarget w = true :=
  uintPrefix_inTarget (.user "x") (symbolicChain_grammar 17) (symbolicChain_grammar 17) w

theorem nearLimit_covered : nearLimit.Covered = true := by decide +kernel

theorem nearLimit_valid : Fml.Valid nearLimit := by
  intro σ v
  rfl

theorem overRawBound_source_size : (symbolicChain 18).size + (symbolicChain 17).size = 72 := by
  decide +kernel

theorem overRawBound_body_nodes : (leafOf? overRawBound).map (fun ψ => ψ.stripAll.2.nodes) = some 517 := by
  decide +kernel

theorem overRawBound_target (w : Waivers) : overRawBound.inTarget w = true :=
  uintPrefix_inTarget (.user "x") (symbolicChain_grammar 18) (symbolicChain_grammar 17) w

theorem overRawBound_notCovered : overRawBound.Covered = false := by decide +kernel

theorem overRawBound_hashFree : overRawBound.hasHash = false :=
  uintPrefix_hashFree (.user "x") (symbolicChain_grammar 18) (symbolicChain_grammar 17)

theorem overRawBound_notHashCovered : overRawBound.hashCovered = false := by
  unfold Fml.hashCovered
  rw [overRawBound_hashFree]
  rfl

private def provedCheck {C : Contract} : LeafVerdict C → Bool
  | .proved => true
  | _ => false
private theorem proved_of_check {C : Contract} (φ : Fml C [])
    (h : provedCheck (decideGoal φ) = true) : decideGoal φ = .proved := by
  cases hd : decideGoal φ with
  | proved => rfl
  | refuted σ => rw [hd] at h; cases h
  | unknown => rw [hd] at h; cases h

/-- This actual proved result is retained despite the two coverage predicates being false. -/
theorem overRawBound_proved : decideGoal overRawBound = .proved :=
  proved_of_check overRawBound (by decide +kernel)
theorem overRawBound_validH : Fml.ValidH overRawBound := decideGoal_sound overRawBound_proved

theorem foldedLarge_exceeds_criterion : 71 < (literalChain 20).size + (literalChain 20).size := by
  decide +kernel

theorem foldedLarge_body_nodes : (leafOf? foldedLarge).map (fun ψ => ψ.stripAll.2.nodes) = some 27 := by
  decide +kernel

theorem foldedLarge_covered : foldedLarge.Covered = true := by decide +kernel

theorem foldedLarge_valid : Fml.Valid foldedLarge := by
  intro σ v
  rfl

theorem foldedLarge_proved : decideGoal foldedLarge = .proved :=
  proved_of_check foldedLarge (by decide +kernel)

theorem fails_grammar : fails.UIntLinear := .sub (.lit _) (.lit _)
theorem fails_folds_to_error : fails.toLT ((SymS.init (C := Bank)).pushQ .uint) =
    some (.err (s := .val .uint)) := by rfl

theorem bothFailed_body_nodes : (leafOf? bothFailed).map (fun ψ => ψ.stripAll.2.nodes) = some 27 := by
  decide +kernel

theorem bothFailed_covered : bothFailed.Covered = true := by decide +kernel

theorem bothFailed_valid : Fml.Valid bothFailed := by
  intro σ v
  rfl

theorem overRawBound_valid : Fml.Valid overRawBound :=
  (Fml.validH_iff overRawBound_hashFree).mp overRawBound_validH

def oneFailed : Fml Bank [] := primitivePrefixEq (.user "unused") fails
  (.app0 (.lit (uintOfNat 0)))

theorem oneFailed_target (w : Waivers) : oneFailed.inTarget w = true :=
  uintPrefix_inTarget (.user "unused") fails_grammar (.lit _) w

theorem oneFailed_covered : oneFailed.Covered = true := by decide +kernel

theorem oneFailed_countermodel : ¬ holds (State.init Bank) oneFailed := by
  intro h
  have hc : holds ((State.init Bank).push (t := .val .uint) (uintOfNat 0))
      (.eq fails (.app0 (.lit (uintOfNat 0)))) := h (uintOfNat 0)
  change (none : Option PrimTy.uint.Denote) = some (uintOfNat 0) at hc
  cases hc

private def refutedCheck {C : Contract} : LeafVerdict C → Bool
  | .refuted _ => true
  | _ => false
private theorem refuted_of_check {C : Contract} (φ : Fml C [])
    (h : refutedCheck (decideGoal φ) = true) :
    ∃ σ : State C [], decideGoal φ = .refuted σ ∧ ¬ Fml.holdsH σ φ := by
  cases hd : decideGoal φ with
  | proved => rw [hd] at h; cases h
  | refuted σ => exact ⟨σ, rfl, decideGoal_refutes hd⟩
  | unknown => rw [hd] at h; cases h

theorem oneFailed_refuted : ∃ σ : State Bank [],
    decideGoal oneFailed = .refuted σ ∧ ¬ Fml.holdsH σ oneFailed :=
  refuted_of_check oneFailed (by decide +kernel)

end Solidity.Examples.DecisionNumericBounds
