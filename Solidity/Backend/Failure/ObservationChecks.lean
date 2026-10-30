import Solidity.Backend.Failure.Observe
import Solidity.Backend.Failure.SliceChecks

/-! Inhabited existing-source controls; malformed bytes remain observable
as bytes even when existing catch decoders reject them. -/
namespace Solidity.Backend.Failure

def witnessContract : Contract := { vars := [] }
def witnessState : State witnessContract [] := State.init witnessContract

theorem assert_source_control :
    TRun.assert (.simple (.bool false)) witnessState = .error .panic :=
  assert_false_intrinsic _ _ rfl

theorem require_source_control :
    TRun.require (.simple (.bool false)) witnessState = .error .revert :=
  require_false_intrinsic _ _ rfl

theorem successful_condition_control :
    TRun.require (.simple (.bool true)) witnessState = .ok ⟨witnessState, List.prefix_refl _⟩ ∧
    TRun.assert (.simple (.bool true)) witnessState = .ok ⟨witnessState, List.prefix_refl _⟩ := by
  constructor <;> rfl

theorem assert_observation_control :
    ResultObserves (fun _ => []) (TRun.assert (.simple (.bool false)) witnessState)
      (.revert (Semantics.encodePanic 1)) :=
  assert_false_observed _ _ rfl _

theorem require_observation_control :
    ResultObserves (fun _ => []) (TRun.require (.simple (.bool false)) witnessState)
      (.revert []) := require_false_observed _ _ rfl _

theorem reason_observation_control :
    ResultObserves (fun _ => [])
      (TRun.revertData [.bytes (Semantics.encodeError [0x62, 0x6f, 0x6f, 0x6d])] witnessState)
      (.revert (Semantics.encodeError [0x62, 0x6f, 0x6f, 0x6d])) := by
  rw [revert_bytes_intrinsic]
  exact .failure (ofData_observes _)

theorem custom_observation_control :
    ResultObserves (fun _ => [])
      (TRun.revertData [.sel "Denied(uint256)", .bytes (Semantics.wordBytes 7)] witnessState)
      (.revert (Semantics.selectorBytes (Semantics.customSelector "Denied(uint256)") ++ Semantics.wordBytes 7)) :=
  custom_parts_observed witnessState "Denied(uint256)" (Semantics.wordBytes 7) _

theorem return_observation_control :
    ResultObserves id (.ok [1, 0, 0xff]) (.success [1, 0, 0xff]) := .success _

theorem malformed_controls :
    Semantics.decodePanic [0x4e, 0x48, 0x7b, 0x71] = none ∧
    Semantics.decodePanic [0x08, 0xc3, 0x79, 0xa0] = none ∧
    Semantics.decodeError [0x08, 0xc3, 0x79, 0xa0] = none ∧
    Semantics.decodeError [0x4e, 0x48, 0x7b, 0x71] = none := by decide

/-- Selector mutations retain the otherwise valid body: neither rejection
can be explained by truncation or a wrong panic length. -/
theorem complete_body_wrong_selector_controls :
    Semantics.decodePanic (Semantics.errorSelector ++ Semantics.wordBytes 1) = none ∧
    Semantics.decodeError (Semantics.panicSelector ++
      (Semantics.encodeError [0x62, 0x6f, 0x6f, 0x6d]).drop 4) = none := by decide

theorem wrong_selector_panic_length :
    (Semantics.errorSelector ++ Semantics.wordBytes 1).length = 36 := by
  simp only [Semantics.errorSelector, Semantics.wordBytes, List.length_append,
    List.length_cons, List.length_nil, List.length_map, List.length_range]

theorem decoder_positive_control :
    Semantics.decodePanic (Semantics.encodePanic 1) = some ⟨1, rfl⟩ ∧
    Semantics.decodeError (Semantics.encodeError [0x62, 0x6f, 0x6f, 0x6d]) =
      some [0x62, 0x6f, 0x6f, 0x6d] := by decide

theorem discriminating_controls :
    Roadmap.Outcome.revert (Semantics.encodePanic 1) ≠ .revert [] ∧
    Roadmap.Outcome.revert (Semantics.encodePanic 1) ≠ .revert (Semantics.encodePanic 0) ∧
    Roadmap.Outcome.revert (Semantics.encodeError []) ≠ .revert [] ∧
    Roadmap.Outcome.revert [0xde, 0xad, 0xbe, 0xef, 0, 1] ≠
      .revert [0xde, 0xad, 0xbe, 0xef, 1, 0] ∧
    Roadmap.Outcome.success [1, 0, 0xff] ≠ .revert [1, 0, 0xff] := by decide

theorem source_emitter_combination :
    Slice.checkedRun (emit 5 (.panic ⟨1, by decide⟩)) markedMachine =
      some ({ markedMachine with memory := Slice.putBytes markedMemory 5 (Semantics.encodePanic 1) },
        some (.revert (Semantics.encodePanic 1))) ∧
    ResultObserves id ((TRun.assert (.simple (.bool false)) witnessState).map (fun _ => []))
      (.revert (Semantics.encodePanic 1)) := by
  apply intrinsic_emission _ (.panic ⟨1, by decide⟩) rfl 5 markedMachine
  · unfold Fits Input.bytes
    rw [show (Semantics.encodePanic 1).length = 36 from panic_length ⟨1, by decide⟩]
    decide
  · decide

theorem assert_not_empty :
    ¬ ResultObserves (fun _ => []) (TRun.assert (.simple (.bool false)) witnessState) (.revert []) :=
  wrong_observation assert_observation_control discriminating_controls.1

theorem assert_not_wrong_code :
    ¬ ResultObserves (fun _ => []) (TRun.assert (.simple (.bool false)) witnessState)
      (.revert (Semantics.encodePanic 0)) :=
  wrong_observation assert_observation_control discriminating_controls.2.1

theorem require_not_panic :
    ¬ ResultObserves (fun _ => []) (TRun.require (.simple (.bool false)) witnessState)
      (.revert (Semantics.encodePanic 1)) :=
  wrong_observation require_observation_control (Ne.symm discriminating_controls.1)

theorem custom_not_wrong_arguments :
    ¬ ResultObserves (fun _ => [])
      (TRun.revertData [.bytes [0xde, 0xad, 0xbe, 0xef, 0, 1]] witnessState)
      (.revert [0xde, 0xad, 0xbe, 0xef, 1, 0]) := by
  apply wrong_observation (correct := .revert [0xde, 0xad, 0xbe, 0xef, 0, 1])
  · rw [revert_bytes_intrinsic]
    exact .failure (ofData_observes _)
  · decide

theorem return_not_revert :
    ¬ ResultObserves id (.ok [1, 0, 0xff]) (.revert [1, 0, 0xff]) :=
  wrong_observation return_observation_control discriminating_controls.2.2.2.2

theorem unsupported_halts_control :
    inputOfResult (.error .diverge) = none ∧ inputOfResult (.error .exhausted) = none := by
  constructor <;> rfl

theorem malformed_still_observed :
    ResultObserves id (.error (.revertWith [0x4e, 0x48, 0x7b, 0x71]))
      (.revert [0x4e, 0x48, 0x7b, 0x71]) := .failure (.data _)

/-- info: 'Solidity.Backend.Failure.intrinsic_emission' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intrinsic_emission
/-- info: 'Solidity.Backend.Failure.assert_false_intrinsic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assert_false_intrinsic
/-- info: 'Solidity.Backend.Failure.require_false_intrinsic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms require_false_intrinsic
/-- info: 'Solidity.Backend.Failure.custom_parts_intrinsic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms custom_parts_intrinsic
/-- info: 'Solidity.Backend.Failure.custom_parts_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms custom_parts_observed
/-- info: 'Solidity.Backend.Failure.source_emitter_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_emitter_combination
end Solidity.Backend.Failure
