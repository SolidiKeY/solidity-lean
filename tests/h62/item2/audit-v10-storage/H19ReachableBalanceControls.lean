import Solidity.Backend.WorldCalls.SourceCallHistoryControls

/-! H19 regression: derive range from existing concrete Source execution
outcomes rather than assuming Fits. This observes the original funding-success
and nonpayable-revert fixtures without copying their programs or interpreters.
It is supporting range evidence for two named current statements, not an exact
H57 old/current transport, a global world/journal invariant, or library/P8
admission/origin/session adequacy. Monetary boundary counterexamples remain in
the published Monetary/MonetaryWorld modules and are not duplicated here. -/
namespace H19.ReachableBalanceControls
open Solidity.Source
open Solidity.Source.SemanticsExamples
open Solidity.Backend.WorldCalls.SourceCallHistoryControls

/-- Actual account observations, not replacement Source states or a new model. -/
def observations : List Monetary.Balance :=
  [(funded.2.2.ex.world.accounts thisC).balance,
   (funded.2.2.ex.world.accounts other).balance,
   (nonpayable.2.2.ex.world.accounts thisC).balance,
   (nonpayable.2.2.ex.world.accounts other).balance]

/-- Values come from the original published execution proofs. -/
theorem observed_values : observations = [7, 3, 10, 0] := by
  unfold observations
  rw [funding_balances.1, funding_balances.2,
    nonpayable_balance_rollback.1, nonpayable_balance_rollback.2]

/-- Joint success/revert outcomes and derived bounds for exactly these observations.
No Fits premise is supplied by the caller. -/
theorem execution_ranges : funded.1 = .ok true ∧
    nonpayable.1 = .ok (.revert []) ∧
    ∀ balance ∈ observations, Monetary.Fits balance := by
  refine ⟨funding_success, nonpayable_reverts, ?_⟩
  intro balance member
  rw [observed_values] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

/-- Ordered word observations are lossless because the actual range was proved.
This does not reconstruct the frozen old Word-valued Account interface. -/
theorem lossless_observations :
    observations.map (fun balance => (Monetary.wordView balance).val) = observations := by
  calc
    _ = observations.map (fun balance => balance) :=
      List.map_congr_left (fun balance member =>
        Monetary.wordView_exact balance (execution_ranges.2.2 balance member))
    _ = observations := List.map_id' observations

/-- info: 'H19.ReachableBalanceControls.observed_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observed_values
/-- info: 'H19.ReachableBalanceControls.execution_ranges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms execution_ranges
/-- info: 'H19.ReachableBalanceControls.lossless_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lossless_observations
end H19.ReachableBalanceControls
