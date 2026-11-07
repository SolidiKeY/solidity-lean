import Solidity.Calculus.DecisionNumericFlatten
import Solidity.Examples.DecisionNumericGround
import Solidity.Examples.DecisionNumericBounds

/-! # Actual numeric flattening resources and uncapped traversal controls
This stage does not enlarge the decision fragment or later compiler budgets.
-/
namespace Solidity.Examples.DecisionNumericFlatten
open Solidity.Decide
open Solidity.Examples.DecisionCoefficientBoundary (Bank)
set_option Elab.async false

def failedSeq : LTm Bank (.val .uint) := .seq (.err (s := .val .uint)) (.app0 (.lit (uintOfNat 0)))
def base : LFml Bank := LFml.optEq failedSeq (.err (s := .val .uint))
def bulk : Nat → LFml Bank
  | 0 => base
  | n + 1 => .and .tt (bulk n)
def oversized : LFml Bank := bulk 238

theorem failedSeq_grammar : failedSeq.Num (fun _ => False) (fun _ => False) :=
  .seq .err (.lit _)
theorem base_grammar : base.UIntQF (fun _ => False) (fun _ => False) :=
  .optEq failedSeq_grammar .err

theorem bulk_grammar (n : Nat) : (bulk n).UIntQF (fun _ => False) (fun _ => False) := by
  induction n with
  | zero => exact base_grammar
  | succ n ih => exact .and .tt ih

theorem bulk_nodes (n : Nat) : (bulk n).nodes = base.nodes + 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bulk, LFml.nodes, ih, Nat.mul_add, Nat.mul_one]
    omega

theorem oversized_nodes : oversized.nodes = 517 := by
  rw [oversized, bulk_nodes]
  rfl

/-- Actual flattener success beyond the unchanged global511-node test. -/
theorem oversized_actual_flatten : ∃ a : FlattenedFormula oversized 0,
    flattenFormulaAt? oversized.nodes 0 oversized = some a ∧
      a.formula = oversized ∧ a.reads = [] :=
  numeric_formula_flattenAt_nodes (bulk_grammar 238) 0

theorem oversized_zero_remainder : ∃ a : FlattenedFormula oversized 0,
    flattenFormulaFuel? oversized.depth oversized.nodes oversized 0 = some (a, 0) ∧
      a.formula = oversized ∧ a.reads = [] :=
  numeric_formula_flatten_zero (bulk_grammar 238) 0

/-- The unchanged exact-route node cap still refuses this same body. -/
theorem oversized_existing_cap : oversized.exactBounded = false := by
  have hg : oversized.UIntQF (fun _ => False) (fun _ => False) := bulk_grammar 238
  have hshape : oversized.allDepth = 0 ∧ oversized.stripAll = ([], oversized) :=
    source_body_shape (hg.source false true)
  have hz : oversized.conds = 0 := hg.conds
  have hlift : oversized.liftCond condLiftFuel = oversized := by
    simpa only [LFml.condSimp_of_conds _ hz] using
      LFml.liftCond_condSimp_of_conds condLiftFuel oversized hz
  have hcut : oversized.cutAll = oversized := by simp only [LFml.cutAll, hg.cut_identity]
  simp only [LFml.exactBounded, hlift, hshape.2, hcut, oversized_nodes]
  rfl

/-- Failed sequencing is preserved as failure, rather than made a returning atom. -/
theorem partial_evaluation (g : State Bank []) (ν : AEnv) : failedSeq.eval g ν = none := by rfl

theorem base_inhabited (g : State Bank []) (ν : AEnv) : base.holds g ν :=
  (LFml.optEq_holds _ _ _ _).mpr rfl

theorem bulk_valid (n : Nat) : (bulk n).Valid := by
  induction n with
  | zero => exact base_inhabited
  | succ n ih => intro g ν; exact ⟨trivial, ih g ν⟩

/-- Strict equality on the same failed reading remains false. -/
theorem strict_partial_refuted (g : State Bank []) (ν : AEnv) :
    ¬ (LFml.eq failedSeq (.app0 (.lit (uintOfNat 0)))).holds g ν := by
  intro h
  exact h

/-- Depth and shared-node failures are tested independently. -/
theorem insufficient_resources :
    (flattenFuel? 1 3 failedSeq 0).isSome = false ∧
    (flattenFuel? 2 2 failedSeq 0).isSome = false := by decide +kernel

theorem exact_term_resources : flattenFuel? 2 3 failedSeq 0 =
    some (Flattened.pure failedSeq 0, 0) := by
  simpa only [failedSeq, LTm.nodes, Nat.sub_self] using
    numeric_flattenFuel failedSeq_grammar 2 3 0 (by decide +kernel) (by decide +kernel)

/-- Existing global coverage and verdict observations are separate and unchanged. -/
theorem original_oversize_control : DecisionNumericBounds.overRawBound.Covered = false ∧
    decideGoal DecisionNumericBounds.overRawBound = .proved :=
  ⟨DecisionNumericBounds.overRawBound_notCovered, DecisionNumericBounds.overRawBound_proved⟩

end Solidity.Examples.DecisionNumericFlatten
