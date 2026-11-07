import Solidity.Lowering.V07.DoubleAssignment

/-!
Guarded regression: dropping first-destination/second-RHS separation must not
freeze the second operand at its initial value. The actual assignment prefix
below overwrites that RHS before reading it in viaIR. General bounded integer
values expose the reached read and distinguish it from legacy order. This is
a local-prefix boundary, not whole compilation, gas or global feasibility.
-/
namespace Solidity.H62.AuditV07.PairSeparationBoundary
open Solidity.Lowering.V07

abbrev locals {C : Contract} (base : State C []) (t : Source.IntTy)
    (u x z : Int) (hu : t.lo ≤ u ∧ u ≤ t.hi)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi) :=
  ((base.push (t := .val (integerPrim t)) (integerValue t z hz)).push
    (t := .val (integerPrim t)) (integerValue t x hx)).push
    (t := .val (integerPrim t)) (integerValue t u hu)

/-- The first destination is the second RHS, so both viaIR captures contain x. -/
theorem viaIR_reached_read {C : Contract} (base : State C []) (t : Source.IntTy)
    (u x z : Int) (hu : t.lo ≤ u ∧ u ≤ t.hi)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi) :
    (assignAssignPrefix .viaIR (.there (.there .here)) (.there .here)
      (.there (.there .here))).run (locals base t u x z hu hx hz) =
      .ok ⟨((((locals base t u x z hu hx hz).setLocal (.there (.there .here))
        (integerValue t x hx)).setLocal (.there .here) (integerValue t x hx)).push
        (t := .val (integerPrim t)) (integerValue t x hx)).push
        (t := .val (integerPrim t)) (integerValue t x hx), List.prefix_refl _⟩ := rfl

/-- Legacy reads the same RHS before overwriting it, so both captures contain z. -/
theorem legacy_initial_read {C : Contract} (base : State C []) (t : Source.IntTy)
    (u x z : Int) (hu : t.lo ≤ u ∧ u ≤ t.hi)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi) :
    (assignAssignPrefix .legacy (.there (.there .here)) (.there .here)
      (.there (.there .here))).run (locals base t u x z hu hx hz) =
      .ok ⟨((((locals base t u x z hu hx hz).setLocal (.there .here)
        (integerValue t z hz)).setLocal (.there (.there .here)) (integerValue t z hz)).push
        (t := .val (integerPrim t)) (integerValue t z hz)).push
        (t := .val (integerPrim t)) (integerValue t z hz), List.prefix_refl _⟩ := rfl

/-- The reached viaIR read cannot equal the stale RHS when x and z differ. -/
theorem stale_rhs_excluded {C : Contract} (base : State C []) (t : Source.IntTy)
    (u x z : Int) (hu : t.lo ≤ u ∧ u ≤ t.hi)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi) (different : x ≠ z) :
    TEnv.get (.there (.there .here))
      (TEnv.set (.there (.there .here)) (integerValue t x hx)
        (locals base t u x z hu hx hz).env) ≠ integerValue t z hz := by
  intro equal
  exact different (integer_injective t x z hx hz equal)

/-- Actual completed prefix runs differ; replacing the reached RHS by z is observable. -/
theorem pipeline_runs_differ {C : Contract} (base : State C []) (t : Source.IntTy)
    (u x z : Int) (hu : t.lo ≤ u ∧ u ≤ t.hi)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi) (different : x ≠ z) :
    (assignAssignPrefix .viaIR (.there (.there .here)) (.there .here)
      (.there (.there .here))).run (locals base t u x z hu hx hz) ≠
    (assignAssignPrefix .legacy (.there (.there .here)) (.there .here)
      (.there (.there .here))).run (locals base t u x z hu hx hz) := by
  rw [viaIR_reached_read, legacy_initial_read]
  intro equal
  have read := congrArg (fun out : Out C base.H [.val (integerPrim t), .val (integerPrim t),
      .val (integerPrim t), .val (integerPrim t), .val (integerPrim t)] =>
    TEnv.get (C := C) (H := out.st.H) (t := .val (integerPrim t)) .here out.st.env) (Except.ok.inj equal)
  change integerValue t x hx = integerValue t z hz at read
  exact different (integer_injective t x z hx hz read)

#print axioms pipeline_runs_differ
#print axioms viaIR_reached_read
#print axioms legacy_initial_read
#print axioms stale_rhs_excluded
end Solidity.H62.AuditV07.PairSeparationBoundary
