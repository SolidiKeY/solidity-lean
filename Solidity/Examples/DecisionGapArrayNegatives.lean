import Solidity.Examples.DecisionArrayGaps

/-!
# Negative companions of the five array source shapes, decided

The five keyed/field/struct/nested-array blocks of `Examples/DecisionArrayGaps.lean`
are proved by the source literal-chain route. Their false companions — a read
past the bound, or a wrong value inside it — were in-target unknowns. Each is
now refuted at a threshold region (`Calculus/DecisionBlockRefute.lean`): every
dynamic array one past the largest literal, leaves `c` below the bound and `h`
past it (searched among the formula's literals and words different from them;
here the first candidate, `0` and `1`, already refutes), each mapping one default. The countermodel is a symbolic
region, not a list of keys or slots. The positive originals are not refuted.
-/
namespace Solidity.Examples.DecisionGapArrayNegatives
open Solidity.Decide Solidity.Examples.DecisionArrayGaps
set_option Elab.async false
local instance : InContract := ⟨Probe⟩

/-- `rows[k][3]` is past the bound `3`. -/
def belowKeyOut : Fml Probe [] := dl[Probe]{ ∀ uint k;
  (∀ uint i; i < 3 → rows[k][i] = 0) → rows[k][3] = 0 }
/-- `rows[k][1]` is inside the bound, with the wrong value. -/
def belowKeyValue : Fml Probe [] := dl[Probe]{ ∀ uint k;
  (∀ uint i; i < 3 → rows[k][i] = 0) → rows[k][1] = 5 }
/-- A fixed `uint[3]` below a key, its slot `2` past the bound `2`. -/
def fixedKeyOut : Fml Probe [] := dl[Probe]{ ∀ uint k;
  (∀ uint i; i < 2 → fixedRows[k][i] = 0) → fixedRows[k][2] = 0 }
def fieldOut : Fml Probe [] := dl[Probe]{
  (∀ uint i; i < 3 → box.xs[i] = 0) → box.xs[3] = 0 }
def structOut : Fml Probe [] := dl[Probe]{
  (∀ uint i; i < 3 → cells[i].v = 0) → cells[3].v = 0 }
def arrayOut : Fml Probe [] := dl[Probe]{ ∀ uint k;
  (∀ uint i; i < 3 → grid[k][i] = 0) → grid[k][3] = 0 }

def negatives : List (Fml Probe []) :=
  [belowKeyOut, belowKeyValue, fixedKeyOut, fieldOut, structOut, arrayOut]

/-- info: [(true, true, "refuted"), (true, true, "refuted"), (true, true, "refuted"), (true, true, "refuted"),
  (true, true, "refuted"), (true, true, "refuted")] -/
#guard_msgs in #eval negatives.map fun φ => (φ.inTarget {}, φ.Covered,
  match decideGoal φ with | .proved => "proved" | .refuted _ => "refuted" | .unknown => "unknown")

/-- Every companion is in the requested target. -/
theorem targets : negatives.all (Fml.inTarget {}) = true := by decide +kernel
/-- The region search refutes every companion. -/
theorem refutable : negatives.all Fml.blockRefutable = true := by decide +kernel

/-- The positive originals are not refuted by the region search. -/
theorem positives_not_refuted :
    [belowKey, fixedBelowKey, belowField, arrayStruct, arrayArray].all
      (fun φ => !φ.blockRefutable) = true := by decide +kernel

private def refutedCheck : LeafVerdict Probe → Bool
  | .refuted _ => true
  | _ => false

private theorem refuted_of_check (φ : Fml Probe [])
    (h : refutedCheck (decideGoal φ) = true) :
    ∃ σ : State Probe [], decideGoal φ = .refuted σ ∧ ¬ Fml.holdsH σ φ := by
  cases hd : decideGoal φ with
  | proved => rw [hd] at h; cases h
  | refuted σ => exact ⟨σ, rfl, decideGoal_refutes hd⟩
  | unknown => rw [hd] at h; cases h

/-- `rows[k][3] = 0` past the bound: certified refutation. -/
theorem belowKeyOut_refuted : ∃ σ : State Probe [],
    decideGoal belowKeyOut = .refuted σ ∧ ¬ Fml.holdsH σ belowKeyOut :=
  refuted_of_check _ (by decide +kernel)
/-- `rows[k][1] = 5` inside the bound: certified refutation. -/
theorem belowKeyValue_refuted : ∃ σ : State Probe [],
    decideGoal belowKeyValue = .refuted σ ∧ ¬ Fml.holdsH σ belowKeyValue :=
  refuted_of_check _ (by decide +kernel)
/-- `fixedRows[k][2] = 0` past the bound: certified refutation. -/
theorem fixedKeyOut_refuted : ∃ σ : State Probe [],
    decideGoal fixedKeyOut = .refuted σ ∧ ¬ Fml.holdsH σ fixedKeyOut :=
  refuted_of_check _ (by decide +kernel)
/-- `box.xs[3] = 0` past the bound: certified refutation. -/
theorem fieldOut_refuted : ∃ σ : State Probe [],
    decideGoal fieldOut = .refuted σ ∧ ¬ Fml.holdsH σ fieldOut :=
  refuted_of_check _ (by decide +kernel)
/-- `cells[3].v = 0` past the bound: certified refutation. -/
theorem structOut_refuted : ∃ σ : State Probe [],
    decideGoal structOut = .refuted σ ∧ ¬ Fml.holdsH σ structOut :=
  refuted_of_check _ (by decide +kernel)
/-- `grid[k][3] = 0` past the bound: certified refutation. -/
theorem arrayOut_refuted : ∃ σ : State Probe [],
    decideGoal arrayOut = .refuted σ ∧ ¬ Fml.holdsH σ arrayOut :=
  refuted_of_check _ (by decide +kernel)

/-- Every companion is covered, so answered. -/
theorem covered : negatives.all Fml.Covered = true := by decide +kernel

/-- The refutation is the region search's own certificate, independent of `decideGoal`. -/
theorem arrayOut_countermodel : ∃ σ : State Probe [], ¬ holds σ arrayOut := by
  have h : (BlockRefute.refute? arrayOut).isSome = true := by decide +kernel
  obtain ⟨w, _⟩ := Option.isSome_iff_exists.mp h
  exact ⟨w.1, w.2⟩

/--
info: 'Solidity.Examples.DecisionGapArrayNegatives.arrayOut_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms arrayOut_refuted

end Solidity.Examples.DecisionGapArrayNegatives
