import Solidity.Backend.Failure.Composition
import Solidity.Backend.Failure.SliceChecks

/-! Inhabited two-write, overlapping-emitter and return-vs-revert controls. -/
namespace Solidity.Backend.Failure
open Slice

theorem both_payloads_control :
    getBytes (putBytes (putBytes markedMemory 31 [1, 2]) 64 [3, 4, 5]) 31 2 = [1, 2] ∧
    getBytes (putBytes (putBytes markedMemory 31 [1, 2]) 64 [3, 4, 5]) 64 3 = [3, 4, 5] :=
  disjoint_payloads markedMemory 31 64 [1, 2] [3, 4, 5] (Or.inl (by decide))

theorem two_executed_writes_control :
    run ((writes 31 [1, 2] ++ writes 64 [3, 4, 5]) ++
      [pushNat 2, pushNat 31, .op .RETURN]) markedMachine =
    some (⟨markedMachine.stack, putBytes (putBytes markedMemory 31 [1, 2]) 64 [3, 4, 5]⟩,
      some (.success [1, 2])) := by
  rw [run_two_writes 31 64 [1, 2] [3, 4, 5] _ _ (by decide) (by decide)]
  rw [run_pushNat 2 (by decide), run_pushNat 31 (by decide)]
  change some ((⟨markedMachine.stack, putBytes (putBytes markedMemory 31 [1, 2]) 64 [3, 4, 5]⟩ : Machine),
    some (Roadmap.Outcome.success (getBytes (putBytes (putBytes markedMemory 31 [1, 2]) 64 [3, 4, 5]) 31 2))) = _
  rw [both_payloads_control.1]

theorem overlapping_suffix_control :
    checkedRun (emit 31 (.custom [1, 2]) ++ emit 31 (.returned [9, 9])) markedMachine =
      some (⟨markedMachine.stack, putBytes markedMemory 31 [1, 2]⟩, some (.revert [1, 2])) :=
  concatenated_emitters 31 31 (.custom [1, 2]) (.returned [9, 9]) markedMachine
    (by unfold Fits Input.bytes; decide) (by decide)

theorem overlapping_writes_negative :
    getBytes (putBytes (putBytes markedMemory 31 [1, 2]) 32 [9]) 31 2 ≠ [1, 2] := by decide

theorem same_bytes_distinct_terminal_control :
    checkedRun (emit 31 (.returned [1, 2])) markedMachine ≠
    checkedRun (emit 31 (.custom [1, 2])) markedMachine :=
  return_revert_execution_distinct 31 [1, 2] markedMachine (by unfold Fits; decide) (by decide)

/-- info: 'Solidity.Backend.Failure.run_two_writes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_two_writes
/-- info: 'Solidity.Backend.Failure.disjoint_payloads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms disjoint_payloads
/-- info: 'Solidity.Backend.Failure.concatenated_emitters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms concatenated_emitters
/-- info: 'Solidity.Backend.Failure.return_revert_execution_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms return_revert_execution_distinct
/-- info: 'Solidity.Backend.Failure.two_executed_writes_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms two_executed_writes_control
end Solidity.Backend.Failure
