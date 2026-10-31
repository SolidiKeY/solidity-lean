import SolidityBridge.RoadmapV15.HaltObservation

namespace SolidityBridge.RoadmapV15.HaltObservationControls
open Solidity Solidity.Roadmap

example : outcomeOfHalt (.success [1, 255]) = .success [1, 255] := rfl
example : outcomeOfHalt (.revert [0, 255]) = .revert [0, 255] := rfl
example : outcomeOfHalt .exceptional = outcomeOfHalt (.revert []) :=
  (outcomeOfHalt_eq_iff _ _).mpr Evm.Halt.observe_exceptional
example : Evm.Halt.exceptional ≠ .revert [] := by decide
example : outcomeOfHalt .exceptional ≠ .revert [0] := by decide
example : outcomeOfHalt (.success []) ≠ outcomeOfHalt .exceptional := by decide
example : outcomeOfHalt (.revert [0, 255]) ≠ .revert [255, 0] := by decide
example : outcomeOfHalt (.revert [0, 255]) = .success [0, 255] ↔
    Evm.Halt.revert [0, 255] = .success [0, 255] := outcomeOfHalt_success_iff _ _
example : outcomeOfHalt .exceptional = .revert [] ↔
    Evm.Halt.exceptional = .revert [] ∨ (Evm.Halt.exceptional = .exceptional ∧ ([] : Evm.Bytes) = []) :=
  outcomeOfHalt_revert_iff _ _

example : (haltOfOutcome (Backend.Failure.Input.custom [0, 255]).observation).observe.2 =
    [0, 255] := input_halt_payload _
example : (haltOfOutcome (Backend.Failure.Input.returned [1, 255]).observation).observe.1 =
    true := input_halt_terminal _
example : (haltOfOutcome (Backend.Failure.Input.custom [1, 255]).observation).observe.1 =
    false := input_halt_terminal _
example : (haltOfOutcome (Backend.Failure.Input.panic ⟨1, by decide⟩).observation).observe.2 =
    Semantics.encodePanic 1 := input_halt_payload _
example : Backend.Failure.ResultObserves id (.ok [1, 255])
    (outcomeOfHalt (haltOfOutcome (Backend.Failure.Input.returned [1, 255]).observation)) :=
  finite_intrinsic_halt_observation _ _ rfl
example : Backend.Failure.ResultObserves id (.error (.revertWith [0, 255]))
    (outcomeOfHalt (haltOfOutcome (Backend.Failure.Input.custom [0, 255]).observation)) :=
  finite_intrinsic_halt_observation _ _ rfl
-- Resource exhaustion/divergence are deliberately not completed observations.
example : Backend.Failure.inputOfResult (.error .exhausted) = none := rfl
example : Backend.Failure.inputOfResult (.error .diverge) = none := rfl

-- Actual G01 event constructors and G06 halt observations; not an execution.
private def request : Event := .call 7 9 [1, 2] false
private def complete : Prefix Event Evm.Halt :=
  ⟨[request, .answer (.revert [0, 255]) none], some (.revert [0, 255])⟩
private def finiteAt (r : Nat) : Prefix Event Evm.Halt :=
  if r = 0 then ⟨[request], none⟩ else complete

private theorem finiteAt_consistent : Prefixes.Consistent finiteAt := by
  intro r s hrs
  by_cases hr : r = 0
  · subst r
    by_cases hs : s = 0
    · subst s; exact Prefix.Le.refl _
    · simp only [finiteAt, ↓reduceIte, if_neg hs]
      exact ⟨by decide, .inl rfl⟩
  · have hs : s ≠ 0 := by omega
    simp only [finiteAt, if_neg hr, if_neg hs]
    exact Prefix.Le.refl _

example : Prefixes.Consistent (fun r => mapPrefix id outcomeOfHalt (finiteAt r)) :=
  mapPrefix_consistent id outcomeOfHalt finiteAt finiteAt_consistent
example : mapPrefix id outcomeOfHalt complete =
    ⟨[request, .answer (.revert [0, 255]) none], some (.revert [0, 255])⟩ :=
  halt_prefix_completed complete _ rfl
example : (mapPrefix id outcomeOfHalt (finiteAt 0)).final = none := rfl
example : (mapPrefix id outcomeOfHalt (finiteAt 1)).final ≠ some (.revert [0]) := by decide
example : Prefixes.Completes (fun r => mapPrefix id outcomeOfHalt (finiteAt r))
    (.revert [0, 255]) :=
  mapPrefix_completes id outcomeOfHalt finiteAt (.revert [0, 255]) ⟨1, rfl⟩
example : ∃ r : Nat, 0 < r := ⟨1, by decide⟩
example : Prefixes.Diverges (fun r : Nat => 0 < r)
    (fun _ => mapPrefix id outcomeOfHalt (⟨[request], none⟩ : Prefix Event Evm.Halt)) :=
  (mapPrefix_diverges_iff (fun r : Nat => 0 < r) id outcomeOfHalt
    (fun _ => (⟨[request], none⟩ : Prefix Event Evm.Halt))).mpr (fun _ _ => rfl)

#print axioms outcomeOfHalt_section
#print axioms haltOfOutcome_observe
#print axioms outcomeOfHalt_eq_iff
#print axioms outcomeOfHalt_success_iff
#print axioms outcomeOfHalt_revert_iff
#print axioms input_halt_payload
#print axioms input_halt_terminal
#print axioms halt_prefix_completed
#print axioms finite_intrinsic_halt_observation
end SolidityBridge.RoadmapV15.HaltObservationControls
