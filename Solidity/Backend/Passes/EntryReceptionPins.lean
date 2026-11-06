import Solidity.Backend.Passes.EntryReceptionControls

/-! Exact standard-only guards, observed on canonical public099. -/
/-- info: 'Solidity.Backend.Passes.EntryReception.decoded_repr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.EntryReception.decoded_repr
/-- info: 'Solidity.Backend.Passes.EntryReception.provisioned_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.EntryReception.provisioned_word
/-- info: 'Solidity.Backend.Passes.EntryReception.admitted_reception' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.EntryReception.admitted_reception
/-- info: 'Solidity.Backend.Passes.EntryReception.zero_admitted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.EntryReception.zero_admitted
/-- info: 'Solidity.Backend.Passes.EntryReception.one_admitted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.EntryReception.one_admitted
/-- info: 'Solidity.Backend.Passes.EntryReception.one_actual_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.EntryReception.one_actual_revert
/-- info: 'Solidity.Backend.Passes.EntryReception.zero_actual_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.EntryReception.zero_actual_success
/-- info: 'Solidity.Backend.Passes.EntryReception.dirty_two_before_body' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.EntryReception.dirty_two_before_body
/-- info: 'Solidity.Backend.Passes.EntryReception.dirty_two_cannot_be_handed_off' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.EntryReception.dirty_two_cannot_be_handed_off
/-- info: 'Solidity.Backend.Passes.EntryReceptionControls.admitted_complete_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.EntryReceptionControls.admitted_complete_vectors
/-- info: 'Solidity.Backend.Passes.EntryReceptionControls.wrong_order_after_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.EntryReceptionControls.wrong_order_after_admission
/-- info: 'Solidity.Backend.Passes.EntryReceptionControls.wrong_projection' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.EntryReceptionControls.wrong_projection
/-- info: 'Solidity.Backend.Passes.EntryReceptionControls.corrupted_saved_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.EntryReceptionControls.corrupted_saved_tail
/-- info: 'Solidity.Backend.Passes.EntryReceptionControls.short_calldata_entry_failure' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.EntryReceptionControls.short_calldata_entry_failure
