import Solidity.Frontend.ConstantDepth.Controls

/-! Exact axiom pins for every theorem in `Solidity.Frontend.ConstantDepth` (SOL-CB);
the same pins close `Controls.lean`, so the library build enforces them too. -/

/-- info: 'Solidity.Frontend.ConstantDepth.mem_constDeps_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.mem_constDeps_iff
/-- info: 'Solidity.Frontend.ConstantDepth.mem_constNodes_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.mem_constNodes_iff
/-- info: 'Solidity.Frontend.ConstantDepth.constNodes_length_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.constNodes_length_le
/-- info: 'Solidity.Frontend.ConstantDepth.reaches_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.reaches_iff
/-- info: 'Solidity.Frontend.ConstantDepth.rank_le_decls' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.rank_le_decls
/-- info: 'Solidity.Frontend.ConstantDepth.filter_length_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.filter_length_mono
/-- info: 'Solidity.Frontend.ConstantDepth.filter_length_strict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.filter_length_strict
/-- info: 'Solidity.Frontend.ConstantDepth.no_self_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.no_self_path
/-- info: 'Solidity.Frontend.ConstantDepth.rank_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.rank_lt
/-- info: 'Solidity.Frontend.ConstantDepth.rank_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.rank_mono
/-- info: 'Solidity.Frontend.ConstantDepth.rank_lt_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.rank_lt_path
/-- info: 'Solidity.Frontend.ConstantDepth.rank_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.rank_pos
/-- info: 'Solidity.Frontend.ConstantDepth.walk_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.walk_rank
/-- info: 'Solidity.Frontend.ConstantDepth.walk_length_lt_decls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.walk_length_lt_decls
/-- info: 'Solidity.Frontend.ConstantDepth.declared_identity' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.declared_identity
/-- info: 'Solidity.Frontend.ConstantDepth.lookup_identity' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.lookup_identity
/-- info: 'Solidity.Frontend.ConstantDepth.constant_not_overload' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.constant_not_overload
/-- info: 'Solidity.Frontend.ConstantDepth.constant_clash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.constant_clash
/-- info: 'Solidity.Frontend.ConstantDepth.singleton_of_pairwise' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.singleton_of_pairwise
/-- info: 'Solidity.Frontend.ConstantDepth.declared_constant_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.declared_constant_singleton
/-- info: 'Solidity.Frontend.ConstantDepth.linearize_starts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.linearize_starts
/-- info: 'Solidity.Frontend.ConstantDepth.lookup_own_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.lookup_own_singleton
/-- info: 'Solidity.Frontend.ConstantDepth.lookup_constant_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.lookup_constant_canonical
/-- info: 'Solidity.Frontend.ConstantDepth.initializer_dependency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.initializer_dependency
/-- info: 'Solidity.Frontend.ConstantDepth.rank_resolved_dependency_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.rank_resolved_dependency_lt
/-- info: 'Solidity.Frontend.ConstantDepth.constBin_paths' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.constBin_paths
/-- info: 'Solidity.Frontend.ConstantDepth.teval_with_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.teval_with_oracle
/-- info: 'Solidity.Frontend.ConstantDepth.nconst_rank_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.nconst_rank_complete
/-- info: 'Solidity.Frontend.ConstantDepth.nconst_levels_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.nconst_levels_complete
/-- info: 'Solidity.Frontend.ConstantDepth.evalConst_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.evalConst_complete
/-- info: 'Solidity.Frontend.ConstantDepth.evalConst_resolved_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.evalConst_resolved_complete
/-- info: 'Solidity.Frontend.ConstantDepth.nconst_resolved_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.nconst_resolved_complete
/-- info: 'Solidity.Frontend.ConstantDepth.evalConst_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.evalConst_iff
/-- info: 'Solidity.Frontend.ConstantDepth.evalConst_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.evalConst_none_iff
/-- info: 'Solidity.Frontend.ConstantDepth.arrayLenB_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.arrayLenB_complete
/-- info: 'Solidity.Frontend.ConstantDepth.arrayLenB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.arrayLenB_iff
/-- info: 'Solidity.Frontend.ConstantDepth.arrayLenB_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.arrayLenB_none_iff
/-- info: 'Solidity.Frontend.ConstantDepth.arrayLenB_resolved_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.arrayLenB_resolved_complete
/-- info: 'Solidity.Frontend.ConstantDepth.teval_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.teval_det
/-- info: 'Solidity.Frontend.ConstantDepth.nconst_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.nconst_det
/-- info: 'Solidity.Frontend.ConstantDepth.arrayLen_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.arrayLen_det
/-- info: 'Solidity.Frontend.ConstantDepth.lookup_declared_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.lookup_declared_constant
/-- info: 'Solidity.Frontend.ConstantDepth.constDeps_declared_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.constDeps_declared_iff
/-- info: 'Solidity.Frontend.ConstantDepth.rank_declared_dependency_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.rank_declared_dependency_lt
/-- info: 'Solidity.Frontend.ConstantDepth.depPath_rank_no_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.depPath_rank_no_return
/-- info: 'Solidity.Frontend.ConstantDepth.teval_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.teval_unique
/-- info: 'Solidity.Frontend.ConstantDepth.nconst_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.nconst_unique
/-- info: 'Solidity.Frontend.ConstantDepth.arrayLen_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.arrayLen_unique
/-- info: 'Solidity.Frontend.ConstantDepth.arrayLen_static_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.arrayLen_static_value
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.noClashB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.noClashB_sound
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.chain_decls' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.chain_decls
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.chain_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.chain_contract
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.chain_rank' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.chain_rank
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.chain_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.chain_value
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.chain_rank_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.chain_rank_tight
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.chain_teval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.chain_teval
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.near_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.near_contract
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.near_rank' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.near_rank
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.near_rank_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.near_rank_tight
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.near_teval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.near_teval
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.diamond_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.diamond_contract
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.diamond_rank' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.diamond_rank
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.diamond_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.diamond_value
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.diamond_teval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.diamond_teval
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.scoped_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.scoped_contract
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.scoped_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.scoped_values
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.scoped_member_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.scoped_member_hidden
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.scoped_no_teval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.scoped_no_teval
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.scoped_teval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.scoped_teval
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.duplicate_clashes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.duplicate_clashes
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.duplicate_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.duplicate_refused
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.cyclic_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.cyclic_refused
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.cyclic_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.cyclic_values
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.unused_cycle_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.unused_cycle_value
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.unused_cycle_teval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.unused_cycle_teval
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.qualified_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.qualified_contract
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.qualified_no_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.qualified_no_edge
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.qualified_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.qualified_refused
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.overflow_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.overflow_contract
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.overflow_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.overflow_values
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.overflow_no_teval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.overflow_no_teval
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.overflow_lengths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.overflow_lengths
/-- info: 'Solidity.Frontend.ConstantDepth.Controls.overflow_length_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ConstantDepth.Controls.overflow_length_refused
