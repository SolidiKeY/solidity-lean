import Solidity.Backend.Passes.MemoryCallReuseFailure

/-! Exact observed standard-only guards for all call-reuse headline proofs and inhabited producers. -/
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.prefix_free' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.prefix_free
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.prefix_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.prefix_source
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.free' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.free
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.costs
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.frames
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.scalar_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.scalar_source
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.alias_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.alias_source
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.void_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.void_source
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.scalar_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.scalar_final
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.alias_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.alias_final
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.void_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.void_final
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.wrong_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.wrong_source
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.public_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.public_calls
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.scalar_fresh_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.scalar_fresh_cost
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.alias_fresh_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.alias_fresh_cost
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.void_fresh_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.void_fresh_cost
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.tuple_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.tuple_source
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.tuple_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.tuple_refused
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.budget
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.input
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.scalar_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.scalar_entry
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.entry
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.following' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.following
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.resources
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.scalar_joined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.scalar_joined
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.scalar_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.scalar_shared
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.alias_joined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.alias_joined
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.alias_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.alias_shared
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.void_joined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.void_joined
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.void_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.void_shared
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.scalar_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.scalar_resources
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.alias_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.alias_resources
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.void_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.void_resources
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.prefix_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.prefix_vector
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.scalar_middle_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.scalar_middle_vector
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.scalar_source_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.scalar_source_vector
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.alias_source_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.alias_source_vector
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.void_source_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.void_source_vector
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.leading_target_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.leading_target_vector
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.scalar_target_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.scalar_target_vector
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.alias_target_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.alias_target_vector
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.void_target_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.void_target_vector
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.scalar_middle_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.scalar_middle_target
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.skipped_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.skipped_effect
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.corrupt_saved_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.corrupt_saved_tail
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.private_cell_changed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.private_cell_changed
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.alias_fresh_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.alias_fresh_identity
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.selected_fresh_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.selected_fresh_base
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.old_addresses' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.old_addresses
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.stale_map_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.stale_map_refused
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseObservations.tuple_source_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseObservations.tuple_source_vector
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseFailure.nonallocating' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseFailure.nonallocating
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseFailure.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseFailure.reached
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseFailure.joined_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseFailure.joined_source
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseFailure.distinct_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseFailure.distinct_source
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseFailure.wrong_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseFailure.wrong_stage
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.leading
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.scalar
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.alias
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.void' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.void
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.wrong
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.scalarFresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.scalarFresh
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.aliasFresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.aliasFresh
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.voidFresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.voidFresh
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.before
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.scalarOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.scalarOut
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.aliasOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.aliasOut
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.voidOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.voidOut
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.scalarFinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.scalarFinal
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.aliasFinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.aliasFinal
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.voidFinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.voidFinal
/-- info: 'Solidity.Backend.Passes.MemoryCallReuse.tupleOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuse.tupleOut
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseApplication.beginning' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseApplication.beginning
/-- info: 'Solidity.Backend.Passes.MemoryCallReuseFailure.unreachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallReuseFailure.unreachable
