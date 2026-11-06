import Solidity.Backend.CalldataPackets.RawInt.Controls

/-! Exact axiom pins for G35-INT-RAW-1105 (Execution and Controls); the same
pins close `Controls.lean`, so the library build enforces them too. -/

/-- info: 'Solidity.Backend.CalldataPackets.RawInt.decode_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.decode_range
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.copy_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.copy_run
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.signed_decode_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.signed_decode_range
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.eval_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.eval_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.guarded_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.guarded_run
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.copy_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.copy_observations
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.range_iff_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.range_iff_accepted
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.accepted_sign_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.accepted_sign_bits
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.accepted_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.accepted_value
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.decode_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.decode_accepted
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.decode_dirty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.decode_dirty
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.decode_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.decode_ok_iff
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.values_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.values_zero
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.values_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.values_succ
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.values_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.values_ok_iff
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.values_dirty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.values_dirty
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.values_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.values_frame
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.guarded_frame_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.guarded_frame_run
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.negative_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.negative_one
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.positive_max' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.positive_max
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.negative_min' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.negative_min
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.dirty_positive' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.dirty_positive
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.dirty_negative' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.dirty_negative
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.dirty_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.dirty_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.positive_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.positive_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.late_dirty_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.late_dirty_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.empty_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.empty_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.eof_padding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.eof_padding
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.zero_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.zero_horizon
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.one_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.one_horizon
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.int8_near_width' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.int8_near_width
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.int16_near_width' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.int16_near_width
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.int248_near_width' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.int248_near_width
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.int256_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.int256_all
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.uint8_near_width' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.uint8_near_width
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.uint256_all' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.uint256_all
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.sign_matters' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.sign_matters
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.negative_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.negative_values
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.near_width_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.near_width_decode
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.negative_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.negative_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.negative_suffix_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.negative_suffix_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.misaligned_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.misaligned_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.unsigned_rejects_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.unsigned_rejects_negative
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.partial_dirty_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.partial_dirty_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.partial_int256_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.partial_int256_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.partial_zero_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.partial_zero_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.entry_frame_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.entry_frame_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.entry_dirty_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.entry_dirty_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.entry_truncated_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.entry_truncated_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.entry_short_head_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.entry_short_head_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.large_entry' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.large_entry
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.entry_large_length_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.entry_large_length_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.unshifted_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.unshifted_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.selector_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.selector_independent
/-- info: 'Solidity.Backend.CalldataPackets.RawInt.Controls.int16_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.CalldataPackets.RawInt.Controls.int16_copy
