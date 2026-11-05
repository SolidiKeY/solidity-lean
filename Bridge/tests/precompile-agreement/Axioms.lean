import SolidityBridge.PrecompileAgreement.Controls

/-! Exact public declaration axiom pins from the actual kernel report. -/

/-- info: 'SolidityBridge.PrecompileAgreement.byte_list' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.byte_list

/-- info: 'SolidityBridge.PrecompileAgreement.byte_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.byte_length

/-- info: 'SolidityBridge.PrecompileAgreement.ofNat_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.ofNat_nat

/-- info: 'SolidityBridge.PrecompileAgreement.subtract_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.subtract_nat

/-- info: 'SolidityBridge.PrecompileAgreement.words_multiple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.words_multiple

/-- info: 'SolidityBridge.PrecompileAgreement.words_next' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.words_next

/-- info: 'SolidityBridge.PrecompileAgreement.words_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.words_last

/-- info: 'SolidityBridge.PrecompileAgreement.words_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.words_boundary

/-- info: 'SolidityBridge.PrecompileAgreement.words_rounding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.words_rounding

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.array' does not depend on any axioms -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.array

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.filled' does not depend on any axioms -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.filled

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.zeros' does not depend on any axioms -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.zeros

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.input

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.lengths' does not depend on any axioms -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.lengths

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.identity_lengths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.identity_lengths

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.sha_lengths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.sha_lengths

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.ripemd_lengths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.ripemd_lengths

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.identity_nonzero_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.identity_nonzero_output

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.identity_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.identity_boundary

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.sha_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.sha_boundary

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.ripemd_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.ripemd_boundary

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.invalid_recovery' does not depend on any axioms -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.invalid_recovery

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.ecrecover_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.ecrecover_controls

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.bad_point' does not depend on any axioms -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.bad_point

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.bnadd_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.bnadd_controls

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.bnmul_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.bnmul_controls

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.pairing_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.pairing_controls

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.blake_one' does not depend on any axioms -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.blake_one

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.blake_bad_flag' does not depend on any axioms -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.blake_bad_flag

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.blake_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.blake_controls

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.blake_short_mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.blake_short_mismatch

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.blake_byte_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.blake_byte_order

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.point_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.point_controls

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.ffi_logical_mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.ffi_logical_mismatch

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.modexp_empty_mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.modexp_empty_mismatch

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.oversized_modexp' does not depend on any axioms -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.oversized_modexp

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.modexp_bound_mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.modexp_bound_mismatch

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.unsupported' does not depend on any axioms -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.unsupported

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.unsupported_core' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.unsupported_core

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.blake_malformed_lengths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.blake_malformed_lengths

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.blake_core_lengths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.blake_core_lengths

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.blake_final_one' does not depend on any axioms -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.blake_final_one

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.blake_final_one_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.blake_final_one_control

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.bls_discount_boundaries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.bls_discount_boundaries

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.blake_high_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.blake_high_header

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.wide_base' does not depend on any axioms -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.wide_base

/-- info: 'SolidityBridge.PrecompileAgreement.Controls.modexp_base_truncation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.Controls.modexp_base_truncation

/-- info: 'SolidityBridge.PrecompileAgreement.address_table' does not depend on any axioms -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.address_table

/-- info: 'SolidityBridge.PrecompileAgreement.address_complete' depends on axioms: [propext] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.address_complete

/-- info: 'SolidityBridge.PrecompileAgreement.sha_price' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.sha_price

/-- info: 'SolidityBridge.PrecompileAgreement.ripemd_price' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.ripemd_price

/-- info: 'SolidityBridge.PrecompileAgreement.pairing_price' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.pairing_price

/-- info: 'SolidityBridge.PrecompileAgreement.ecrecover_gas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.ecrecover_gas

/-- info: 'SolidityBridge.PrecompileAgreement.sha_gas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.sha_gas

/-- info: 'SolidityBridge.PrecompileAgreement.ripemd_gas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.ripemd_gas

/-- info: 'SolidityBridge.PrecompileAgreement.bnadd_gas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.bnadd_gas

/-- info: 'SolidityBridge.PrecompileAgreement.bnmul_gas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.bnmul_gas

/-- info: 'SolidityBridge.PrecompileAgreement.pairing_gas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.pairing_gas

/-- info: 'SolidityBridge.PrecompileAgreement.point_gas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.point_gas

/-- info: 'SolidityBridge.PrecompileAgreement.big_reader' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.big_reader

/-- info: 'SolidityBridge.PrecompileAgreement.first_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.first_four

/-- info: 'SolidityBridge.PrecompileAgreement.zero_padding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.zero_padding

/-- info: 'SolidityBridge.PrecompileAgreement.blake_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.blake_padding

/-- info: 'SolidityBridge.PrecompileAgreement.blake_zero_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.blake_zero_header

/-- info: 'SolidityBridge.PrecompileAgreement.blake_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.blake_price

/-- info: 'SolidityBridge.PrecompileAgreement.blake_gas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.blake_gas

/-- info: 'SolidityBridge.PrecompileAgreement.blake_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.blake_valid

/-- info: 'SolidityBridge.PrecompileAgreement.blake_insufficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.blake_insufficient

/-- info: 'SolidityBridge.PrecompileAgreement.blake_invalid_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.blake_invalid_flag

/-- info: 'SolidityBridge.PrecompileAgreement.blake_valid_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.blake_valid_one

/-- info: 'SolidityBridge.PrecompileAgreement.blake_invalid_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.blake_invalid_size

/-- info: 'SolidityBridge.PrecompileAgreement.blake_zero_gas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.blake_zero_gas

/-- info: 'SolidityBridge.PrecompileAgreement.identity_gas' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.identity_gas

/-- info: 'SolidityBridge.PrecompileAgreement.identity_output' depends on axioms: [propext] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.identity_output

/-- info: 'SolidityBridge.PrecompileAgreement.identity_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.identity_run

/-- info: 'SolidityBridge.PrecompileAgreement.identity_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.identity_success

/-- info: 'SolidityBridge.PrecompileAgreement.identity_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.identity_failure

/-- info: 'SolidityBridge.PrecompileAgreement.identity_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.identity_charged

/-- info: 'SolidityBridge.PrecompileAgreement.identity_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.identity_success_iff

/-- info: 'SolidityBridge.PrecompileAgreement.identity_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.identity_exact

/-- info: 'SolidityBridge.PrecompileAgreement.identity_one_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.identity_one_short

/-- info: 'SolidityBridge.PrecompileAgreement.identity_unaffordable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SolidityBridge.PrecompileAgreement.identity_unaffordable
