import Solidity.Calculus.DecisionNumericCompiler
import Solidity.Examples.DecisionNumericStages
import Solidity.Examples.DecisionNumericFlatten

/-! # Concrete numeric compiler clients above the old aggregate cap
The existing compiler is used; no global coverage/default/verdict is changed.
-/
namespace Solidity.Examples.DecisionNumericCompiler
open Solidity.Decide
open Solidity.Examples.DecisionCoefficientBoundary (Bank)
open Solidity.Examples.DecisionNumericFlatten
set_option Elab.async false

theorem bulk_equationDepth (n : Nat) : (bulk n).equationDepth = base.equationDepth := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bulk, LFml.equationDepth, ih, Nat.zero_max]

theorem oversized_equationDepth : oversized.equationDepth = 2 := by
  rw [oversized, bulk_equationDepth]
  rfl

/-- The same517-node body really compiles; optional failure validity survives. -/
theorem oversized_compiler : ∃ r : LeafArithmetic oversized,
    leafArithmetic? oversized = some r ∧ r.arithmetic.Valid := by
  obtain ⟨r, hr, hc⟩ := numeric_leafArithmetic_certificate (bulk_grammar 238)
    (by change oversized.equationDepth ≤ 1023; rw [oversized_equationDepth]; decide +kernel)
  exact ⟨r, hr, hc.mp (bulk_valid 238)⟩

def strictPartial : LFml Bank := .eq failedSeq (.app0 (.lit (uintOfNat 0)))

theorem strictPartial_grammar : strictPartial.UIntQF (fun _ => False) (fun _ => False) :=
  .eq failedSeq_grammar (.lit _)

/-- The real arithmetic encoding is false for strict failed equality. -/
theorem strictPartial_compiler : ∃ r : LeafArithmetic strictPartial,
    leafArithmetic? strictPartial = some r ∧ ¬ r.arithmetic.Valid := by
  obtain ⟨r, hr, hc⟩ := numeric_leafArithmetic_certificate strictPartial_grammar (by decide +kernel)
  refine ⟨r, hr, fun hv => ?_⟩
  have h : strictPartial.holds (State.init Bank) AEnv.dflt :=
    hc.mpr hv (State.init Bank) AEnv.dflt
  exact strict_partial_refuted (State.init Bank) AEnv.dflt h

/-- Actual positive-prefix source discovery and its actual arithmetic result. -/
theorem original_source_compiler : ∃ ψ : LFml Bank,
    leafOf? DecisionNumericBounds.overRawBound = some (.all 0 .uint ψ) ∧
      ψ.nodes = 517 ∧ ψ.UIntQF (fun q => q = ⟨.uint, 0⟩) (fun _ => False) ∧
      ∃ r : LeafArithmetic ψ, leafArithmetic? ψ = some r ∧ (ψ.Valid ↔ r.arithmetic.Valid) := by
  obtain ⟨ψ, hl, hg, hn, r, hr, hc⟩ := qfUIntPrefix_compiler_stage (.user "x")
    DecisionNumericStages.largeBody_grammar
    (by rw [DecisionNumericStages.source_weight]; decide +kernel)
  change leafOf? DecisionNumericBounds.overRawBound = some (.all 0 .uint ψ) at hl
  have hm : (leafOf? DecisionNumericBounds.overRawBound).map (fun θ => θ.stripAll.2.nodes) = some 517 :=
    DecisionNumericBounds.overRawBound_body_nodes
  have hs : ψ.allDepth = 0 ∧ ψ.stripAll = ([], ψ) := source_body_shape (hg.source false true)
  rw [hl] at hm
  simp only [Option.map_some, LFml.stripAll, hs.2] at hm
  exact ⟨ψ, hl, Option.some.inj hm, hg, r, hr, hc⟩

theorem closed_negative_source_compiler : ∃ ψ : LFml Bank,
    leafOf? DecisionNumericGroundSource.mismatched = some ψ ∧
      ∃ r : LeafArithmetic ψ, leafArithmetic? ψ = some r ∧ (ψ.Valid ↔ r.arithmetic.Valid) := by
  obtain ⟨ψ, hl, hg, hn, r, hr, hc⟩ := qfUIntGround_compiler_stage
    DecisionNumericGroundSource.mismatched_grammar (by decide +kernel)
  exact ⟨ψ, hl, r, hr, hc⟩

theorem oversized_flattenedArithmetic : ∃ r : FlattenedArithmetic oversized,
    flattenedArithmetic? oversized.nodes oversized = some r ∧ r.encoding.arithmetic.Valid := by
  obtain ⟨r, hr, hc⟩ := numeric_flattenedArithmetic_certificate (bulk_grammar 238)
    (by change oversized.equationDepth ≤ 1023; rw [oversized_equationDepth]; decide +kernel)
    oversized.nodes (Nat.le_refl _)
  exact ⟨r, hr, hc.mp (bulk_valid 238)⟩

theorem strictPartial_flattenedArithmetic : ∃ r : FlattenedArithmetic strictPartial,
    flattenedArithmetic? strictPartial.nodes strictPartial = some r ∧ ¬ r.encoding.arithmetic.Valid := by
  obtain ⟨r, hr, hc⟩ := numeric_flattenedArithmetic_certificate strictPartial_grammar
    (by decide +kernel) strictPartial.nodes (Nat.le_refl _)
  refine ⟨r, hr, fun hv => ?_⟩
  exact strict_partial_refuted (State.init Bank) AEnv.dflt (hc.mpr hv (State.init Bank) AEnv.dflt)

theorem oversized_unchanged_default_budget :
    (flattenedArithmetic? 2048 oversized).isSome = true :=
  numeric_flattenedArithmetic_resources (bulk_grammar 238)
    (by change oversized.equationDepth ≤ 1023; rw [oversized_equationDepth]; decide +kernel)
    2048 (by change oversized.nodes ≤ 2048; rw [oversized_nodes]; decide +kernel)

theorem original_source_flattenedArithmetic : ∃ ψ : LFml Bank,
    leafOf? DecisionNumericBounds.overRawBound = some (.all 0 .uint ψ) ∧ ψ.nodes = 517 ∧
      ∃ r : FlattenedArithmetic ψ, flattenedArithmetic? ψ.nodes ψ = some r ∧
        (ψ.Valid ↔ r.encoding.arithmetic.Valid) := by
  obtain ⟨ψ, hl, hn, r, hr, hc⟩ := qfUIntPrefix_flattenedArithmetic_stage (.user "x")
    DecisionNumericStages.largeBody_grammar
    (by rw [DecisionNumericStages.source_weight]; decide +kernel)
  change leafOf? DecisionNumericBounds.overRawBound = some (.all 0 .uint ψ) at hl
  have hm : (leafOf? DecisionNumericBounds.overRawBound).map (fun θ => θ.stripAll.2.nodes) = some 517 :=
    DecisionNumericBounds.overRawBound_body_nodes
  obtain ⟨θ, ht, hg, hnodes⟩ := qfUIntPrefix_leaf_stage (.user "x")
    DecisionNumericStages.largeBody_grammar (by rw [DecisionNumericStages.source_weight]; decide +kernel)
  have heq : θ = ψ := by
    have he : LFml.all 0 .uint θ = LFml.all 0 .uint ψ := Option.some.inj (ht.symm.trans hl)
    cases he
    rfl
  subst θ
  have hs : ψ.allDepth = 0 ∧ ψ.stripAll = ([], ψ) := source_body_shape (hg.source false true)
  rw [hl] at hm
  simp only [Option.map_some, LFml.stripAll, hs.2] at hm
  exact ⟨ψ, hl, Option.some.inj hm, r, hr, hc⟩

def nonlinear : LFml Bank := .eq (p := .uint)
  (.app2 (.binop .mul rfl) (.var 0) (.var 1)) (.app0 (.lit (uintOfNat 1)))

theorem nonlinear_shallow : nonlinear.equationDepth = 2 := by rfl
theorem nonlinear_refused : (leafArithmetic? nonlinear).isSome = false := by decide +kernel

theorem nonlinear_not_grammar : ¬ nonlinear.UIntQF (fun _ => True) (fun _ => True) := by
  intro hg
  have h : (leafArithmetic? nonlinear).isSome = true :=
    numeric_leafArithmetic_of_equationDepth hg (by rw [nonlinear_shallow]; decide +kernel)
  rw [nonlinear_refused] at h
  cases h

theorem nonlinear_countermodel : ¬ nonlinear.holds (State.init Bank) AEnv.dflt := by
  intro h
  exact (by decide +kernel : uintOfNat 0 ≠ uintOfNat 1) h

theorem unchanged_controls : oversized.nodes = 517 ∧ oversized.exactBounded = false ∧
    DecisionNumericBounds.overRawBound.Covered = false ∧
    DecisionNumericBounds.overRawBound.hashCovered = false ∧
    decideGoal DecisionNumericBounds.overRawBound = .proved :=
  ⟨oversized_nodes, oversized_existing_cap, DecisionNumericStages.unchanged_global_cap⟩

end Solidity.Examples.DecisionNumericCompiler
