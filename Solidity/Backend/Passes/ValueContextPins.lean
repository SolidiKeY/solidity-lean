import Solidity.Backend.Passes.ValueContextAllocation

/-! Exact observed standard-only fresh-context axiom guards. -/
/-- info: 'Solidity.Backend.Passes.simple_fresh_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.simple_fresh_code
/-- info: 'Solidity.Backend.Passes.spath_fresh_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.spath_fresh_code
/-- info: 'Solidity.Backend.Passes.loc_fresh_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.loc_fresh_code
/-- info: 'Solidity.Backend.Passes.core_val_fresh_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.core_val_fresh_code
/-- info: 'Solidity.Backend.Passes.simple_fresh_in' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.simple_fresh_in
/-- info: 'Solidity.Backend.Passes.spath_fresh_in' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.spath_fresh_in
/-- info: 'Solidity.Backend.Passes.loc_fresh_in' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.loc_fresh_in
/-- info: 'Solidity.Backend.Passes.core_val_fresh_in' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.core_val_fresh_in
/-- info: 'Solidity.Backend.Passes.ptr_fresh_cert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ptr_fresh_cert
/-- info: 'Solidity.Backend.Passes.val_fresh_cert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.val_fresh_cert
/-- info: 'Solidity.Backend.Passes.value_fresh_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.value_fresh_code
/-- info: 'Solidity.Backend.Passes.value_fresh_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.value_fresh_eval
/-- info: 'Solidity.Backend.Passes.memory_extend_reference' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memory_extend_reference
/-- info: 'Solidity.Backend.Passes.value_after_fresh_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.value_after_fresh_scalar
/-- info: 'Solidity.Backend.Passes.value_after_fresh_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.value_after_fresh_reference
/-- info: 'Solidity.Backend.Passes.value_fresh_scalar_revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.value_fresh_scalar_revert_iff
/-- info: 'Solidity.Backend.Passes.value_fresh_reference_revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.value_fresh_reference_revert_iff
/-- info: 'Solidity.Backend.Passes.ValueContextControls.scalar_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextControls.scalar_source
/-- info: 'Solidity.Backend.Passes.ValueContextControls.reference_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextControls.reference_source
/-- info: 'Solidity.Backend.Passes.ValueContextControls.scalar_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextControls.scalar_run
/-- info: 'Solidity.Backend.Passes.ValueContextControls.reference_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextControls.reference_run
/-- info: 'Solidity.Backend.Passes.ValueContextControls.scalar_decl_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextControls.scalar_decl_prefix
/-- info: 'Solidity.Backend.Passes.ValueContextControls.reference_decl_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextControls.reference_decl_prefix
/-- info: 'Solidity.Backend.Passes.ValueContextControls.preserved_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextControls.preserved_failures
/-- info: 'Solidity.Backend.Passes.ValueContextControls.source_wrong_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextControls.source_wrong_index
/-- info: 'Solidity.Backend.Passes.ValueContextControls.target_wrong_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextControls.target_wrong_index
/-- info: 'Solidity.Backend.Passes.ValueContextControls.core_refusal_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextControls.core_refusal_preserved
/-- info: 'Solidity.Backend.Passes.ValueContextControls.ordered_scalar_memory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextControls.ordered_scalar_memory
/-- info: 'Solidity.Backend.Passes.ValueContextControls.ordered_reference_memory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextControls.ordered_reference_memory
/-- info: 'Solidity.Backend.Passes.ValueContextControls.declaration_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextControls.declaration_failures
/-- info: 'Solidity.Backend.Passes.ValueContextControls.source_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextControls.source_failures
/-- info: 'Solidity.Backend.Passes.ValueContextControls.recognizers_same_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextControls.recognizers_same_code
/-- info: 'Solidity.Backend.Passes.ValueContextAllocation.allocated_reference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextAllocation.allocated_reference
/-- info: 'Solidity.Backend.Passes.ValueContextAllocation.recognizer_same_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextAllocation.recognizer_same_code
/-- info: 'Solidity.Backend.Passes.ValueContextAllocation.ordered_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueContextAllocation.ordered_observations
