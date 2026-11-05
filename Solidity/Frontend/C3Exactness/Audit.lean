import Solidity.Frontend.C3Exactness.Controls
import Solidity.Frontend.C3Exactness.GraphControls

/-! Complete declaration/signature/axiom audit and frozen witness/API type assertions. -/

open Solidity.Source Solidity.Frontend.C3Exactness

#check Solidity.Frontend.C3Exactness.selects
/-- info: 'Solidity.Frontend.C3Exactness.selects' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.selects

#check Solidity.Frontend.C3Exactness.rank
/-- info: 'Solidity.Frontend.C3Exactness.rank' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.rank

#check Solidity.Frontend.C3Exactness.find_getIdx
/-- info: 'Solidity.Frontend.C3Exactness.find_getIdx' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.find_getIdx

#check Solidity.Frontend.C3Exactness.rank_le
/-- info: 'Solidity.Frontend.C3Exactness.rank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.rank_le

#check Solidity.Frontend.C3Exactness.rank_selected
/-- info: 'Solidity.Frontend.C3Exactness.rank_selected' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.rank_selected

#check Solidity.Frontend.C3Exactness.selects_iff
/-- info: 'Solidity.Frontend.C3Exactness.selects_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.selects_iff

#check Solidity.Frontend.C3Exactness.rank_injective
/-- info: 'Solidity.Frontend.C3Exactness.rank_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.rank_injective

#check Solidity.Frontend.C3Exactness.bases_empty_of_rank_eq
/-- info: 'Solidity.Frontend.C3Exactness.bases_empty_of_rank_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.bases_empty_of_rank_eq

#check Solidity.Frontend.C3Exactness.rank_lt_of_base
/-- info: 'Solidity.Frontend.C3Exactness.rank_lt_of_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.rank_lt_of_base

#check Solidity.Frontend.C3Exactness.rank_le_index
/-- info: 'Solidity.Frontend.C3Exactness.rank_le_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.rank_le_index

#check Solidity.Frontend.C3Exactness.base_rank_lt
/-- info: 'Solidity.Frontend.C3Exactness.base_rank_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.base_rank_lt

#check Solidity.Frontend.C3Exactness.rank_name_mem
/-- info: 'Solidity.Frontend.C3Exactness.rank_name_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.rank_name_mem

#check Solidity.Frontend.C3Exactness.rank_graph
/-- info: 'Solidity.Frontend.C3Exactness.rank_graph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.rank_graph

#check Solidity.Frontend.C3Exactness.nodup_subset_length
/-- info: 'Solidity.Frontend.C3Exactness.nodup_subset_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.nodup_subset_length

#check Solidity.Frontend.C3Exactness.public_merge_fuel
/-- info: 'Solidity.Frontend.C3Exactness.public_merge_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.public_merge_fuel

#check Solidity.Frontend.C3Exactness.Controls.choiceFamily
/-- info: 'Solidity.Frontend.C3Exactness.Controls.choiceFamily' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.choiceFamily

#check Solidity.Frontend.C3Exactness.Controls.blocked_prefix
/-- info: 'Solidity.Frontend.C3Exactness.Controls.blocked_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.blocked_prefix

#check Solidity.Frontend.C3Exactness.Controls.legal_last
/-- info: 'Solidity.Frontend.C3Exactness.Controls.legal_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.legal_last

#check Solidity.Frontend.C3Exactness.Controls.every_head_position
/-- info: 'Solidity.Frontend.C3Exactness.Controls.every_head_position' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.every_head_position

#check Solidity.Frontend.C3Exactness.Controls.cycle_obstruction
/-- info: 'Solidity.Frontend.C3Exactness.Controls.cycle_obstruction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.cycle_obstruction

#check Solidity.Frontend.C3Exactness.Controls.duplicate_obstruction
/-- info: 'Solidity.Frontend.C3Exactness.Controls.duplicate_obstruction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.duplicate_obstruction

#check Solidity.Frontend.C3Exactness.Controls.identity_trace
/-- info: 'Solidity.Frontend.C3Exactness.Controls.identity_trace' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.identity_trace

#check Solidity.Frontend.C3Exactness.Controls.last_head_control
/-- info: 'Solidity.Frontend.C3Exactness.Controls.last_head_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.last_head_control

#check Solidity.Frontend.C3Exactness.Controls.empty_zero_fuel
/-- info: 'Solidity.Frontend.C3Exactness.Controls.empty_zero_fuel' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.empty_zero_fuel

#check Solidity.Frontend.C3Exactness.Controls.empty_one_fuel
/-- info: 'Solidity.Frontend.C3Exactness.Controls.empty_one_fuel' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.empty_one_fuel

#check Solidity.Frontend.C3Exactness.Controls.singleton_insufficient
/-- info: 'Solidity.Frontend.C3Exactness.Controls.singleton_insufficient' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.singleton_insufficient

#check Solidity.Frontend.C3Exactness.Controls.singleton_sufficient
/-- info: 'Solidity.Frontend.C3Exactness.Controls.singleton_sufficient' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.singleton_sufficient

#check Solidity.Frontend.C3Exactness.Controls.independent_heads
/-- info: 'Solidity.Frontend.C3Exactness.Controls.independent_heads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.independent_heads

#check Solidity.Frontend.C3Exactness.Controls.later_head_refused
/-- info: 'Solidity.Frontend.C3Exactness.Controls.later_head_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.later_head_refused

#check Solidity.Frontend.C3Exactness.Controls.diamond_merge
/-- info: 'Solidity.Frontend.C3Exactness.Controls.diamond_merge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.diamond_merge

#check Solidity.Frontend.C3Exactness.Controls.repeated_shared_merge
/-- info: 'Solidity.Frontend.C3Exactness.Controls.repeated_shared_merge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.repeated_shared_merge

#check Solidity.Frontend.C3Exactness.Controls.cycle_refused
/-- info: 'Solidity.Frontend.C3Exactness.Controls.cycle_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.cycle_refused

#check Solidity.Frontend.C3Exactness.Controls.delayed_obstruction
/-- info: 'Solidity.Frontend.C3Exactness.Controls.delayed_obstruction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.delayed_obstruction

#check Solidity.Frontend.C3Exactness.Controls.delayed_refused
/-- info: 'Solidity.Frontend.C3Exactness.Controls.delayed_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.delayed_refused

#check Solidity.Frontend.C3Exactness.Controls.empty_trace
/-- info: 'Solidity.Frontend.C3Exactness.Controls.empty_trace' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.empty_trace

#check Solidity.Frontend.C3Exactness.Controls.cycle_stuck
/-- info: 'Solidity.Frontend.C3Exactness.Controls.cycle_stuck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.cycle_stuck

#check Solidity.Frontend.C3Exactness.graphSpecs
/-- info: 'Solidity.Frontend.C3Exactness.graphSpecs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphSpecs

#check Solidity.Frontend.C3Exactness.graphUnit
/-- info: 'Solidity.Frontend.C3Exactness.graphUnit' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphUnit

#check Solidity.Frontend.C3Exactness.graphDiamond
/-- info: 'Solidity.Frontend.C3Exactness.graphDiamond' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDiamond

#check Solidity.Frontend.C3Exactness.graphDiamond_admitted
/-- info: 'Solidity.Frontend.C3Exactness.graphDiamond_admitted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDiamond_admitted

#check Solidity.Frontend.C3Exactness.graphDiamond_public
/-- info: 'Solidity.Frontend.C3Exactness.graphDiamond_public' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDiamond_public

#check Solidity.Frontend.C3Exactness.graphDiamond_exact
/-- info: 'Solidity.Frontend.C3Exactness.graphDiamond_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDiamond_exact

#check Solidity.Frontend.C3Exactness.graphDiamond_constructors
/-- info: 'Solidity.Frontend.C3Exactness.graphDiamond_constructors' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDiamond_constructors

#check Solidity.Frontend.C3Exactness.graphDiamond_identities
/-- info: 'Solidity.Frontend.C3Exactness.graphDiamond_identities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDiamond_identities

#check Solidity.Frontend.C3Exactness.graphDiamond_graph_nodes
/-- info: 'Solidity.Frontend.C3Exactness.graphDiamond_graph_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDiamond_graph_nodes

#check Solidity.Frontend.C3Exactness.graphDiamond_identity_order_refused
/-- info: 'Solidity.Frontend.C3Exactness.graphDiamond_identity_order_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDiamond_identity_order_refused

#check Solidity.Frontend.C3Exactness.graphShared
/-- info: 'Solidity.Frontend.C3Exactness.graphShared' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphShared

#check Solidity.Frontend.C3Exactness.graphShared_admitted
/-- info: 'Solidity.Frontend.C3Exactness.graphShared_admitted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphShared_admitted

#check Solidity.Frontend.C3Exactness.graphShared_public
/-- info: 'Solidity.Frontend.C3Exactness.graphShared_public' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphShared_public

#check Solidity.Frontend.C3Exactness.graphShared_exact
/-- info: 'Solidity.Frontend.C3Exactness.graphShared_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphShared_exact

#check Solidity.Frontend.C3Exactness.graphShared_constructor_nodup
/-- info: 'Solidity.Frontend.C3Exactness.graphShared_constructor_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphShared_constructor_nodup

#check Solidity.Frontend.C3Exactness.graphShared_constructors
/-- info: 'Solidity.Frontend.C3Exactness.graphShared_constructors' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphShared_constructors

#check Solidity.Frontend.C3Exactness.graphRedundant
/-- info: 'Solidity.Frontend.C3Exactness.graphRedundant' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphRedundant

#check Solidity.Frontend.C3Exactness.graphRedundant_admitted
/-- info: 'Solidity.Frontend.C3Exactness.graphRedundant_admitted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphRedundant_admitted

#check Solidity.Frontend.C3Exactness.graphRedundant_public
/-- info: 'Solidity.Frontend.C3Exactness.graphRedundant_public' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphRedundant_public

#check Solidity.Frontend.C3Exactness.graphRedundant_constructors
/-- info: 'Solidity.Frontend.C3Exactness.graphRedundant_constructors' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphRedundant_constructors

#check Solidity.Frontend.C3Exactness.graphBad
/-- info: 'Solidity.Frontend.C3Exactness.graphBad' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphBad

#check Solidity.Frontend.C3Exactness.graphBad_admitted
/-- info: 'Solidity.Frontend.C3Exactness.graphBad_admitted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphBad_admitted

#check Solidity.Frontend.C3Exactness.graphBad_merge_stuck
/-- info: 'Solidity.Frontend.C3Exactness.graphBad_merge_stuck' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphBad_merge_stuck

#check Solidity.Frontend.C3Exactness.graphBad_certificate
/-- info: 'Solidity.Frontend.C3Exactness.graphBad_certificate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphBad_certificate

#check Solidity.Frontend.C3Exactness.graphBad_all_fuel
/-- info: 'Solidity.Frontend.C3Exactness.graphBad_all_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphBad_all_fuel

#check Solidity.Frontend.C3Exactness.graphBad_public_refused
/-- info: 'Solidity.Frontend.C3Exactness.graphBad_public_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphBad_public_refused

#check Solidity.Frontend.C3Exactness.graphBad_inherited_certificate
/-- info: 'Solidity.Frontend.C3Exactness.graphBad_inherited_certificate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphBad_inherited_certificate

#check Solidity.Frontend.C3Exactness.graphBad_inherited_all_fuel
/-- info: 'Solidity.Frontend.C3Exactness.graphBad_inherited_all_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphBad_inherited_all_fuel

#check Solidity.Frontend.C3Exactness.graphBad_identity_stuck
/-- info: 'Solidity.Frontend.C3Exactness.graphBad_identity_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphBad_identity_stuck

#check Solidity.Frontend.C3Exactness.graphSelfCycle
/-- info: 'Solidity.Frontend.C3Exactness.graphSelfCycle' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphSelfCycle

#check Solidity.Frontend.C3Exactness.graphSelfCycle_not_admitted
/-- info: 'Solidity.Frontend.C3Exactness.graphSelfCycle_not_admitted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphSelfCycle_not_admitted

#check Solidity.Frontend.C3Exactness.graphSelfCycle_path
/-- info: 'Solidity.Frontend.C3Exactness.graphSelfCycle_path' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphSelfCycle_path

#check Solidity.Frontend.C3Exactness.graphSelfCycle_all_fuel
/-- info: 'Solidity.Frontend.C3Exactness.graphSelfCycle_all_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphSelfCycle_all_fuel

#check Solidity.Frontend.C3Exactness.graphMutualCycle
/-- info: 'Solidity.Frontend.C3Exactness.graphMutualCycle' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphMutualCycle

#check Solidity.Frontend.C3Exactness.graphMutualCycle_not_admitted
/-- info: 'Solidity.Frontend.C3Exactness.graphMutualCycle_not_admitted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphMutualCycle_not_admitted

#check Solidity.Frontend.C3Exactness.graphMutualCycle_path
/-- info: 'Solidity.Frontend.C3Exactness.graphMutualCycle_path' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphMutualCycle_path

#check Solidity.Frontend.C3Exactness.graphMutualCycle_all_fuel
/-- info: 'Solidity.Frontend.C3Exactness.graphMutualCycle_all_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphMutualCycle_all_fuel

#check Solidity.Frontend.C3Exactness.graphMutualCycle_fallback
/-- info: 'Solidity.Frontend.C3Exactness.graphMutualCycle_fallback' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphMutualCycle_fallback

#check Solidity.Frontend.C3Exactness.graphEmpty
/-- info: 'Solidity.Frontend.C3Exactness.graphEmpty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphEmpty

#check Solidity.Frontend.C3Exactness.graphEmpty_admitted
/-- info: 'Solidity.Frontend.C3Exactness.graphEmpty_admitted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphEmpty_admitted

#check Solidity.Frontend.C3Exactness.graphUnknown_public
/-- info: 'Solidity.Frontend.C3Exactness.graphUnknown_public' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphUnknown_public

#check Solidity.Frontend.C3Exactness.graphUnknown_identity_refused
/-- info: 'Solidity.Frontend.C3Exactness.graphUnknown_identity_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphUnknown_identity_refused

#check Solidity.Frontend.C3Exactness.graphSentinel_not_global_injective
/-- info: 'Solidity.Frontend.C3Exactness.graphSentinel_not_global_injective' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphSentinel_not_global_injective

#check Solidity.Frontend.C3Exactness.graphDiamond_refl
/-- info: 'Solidity.Frontend.C3Exactness.graphDiamond_refl' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDiamond_refl

#check Solidity.Frontend.C3Exactness.graphDiamond_reaches
/-- info: 'Solidity.Frontend.C3Exactness.graphDiamond_reaches' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDiamond_reaches

#check Solidity.Frontend.C3Exactness.graphDiamond_C_public
/-- info: 'Solidity.Frontend.C3Exactness.graphDiamond_C_public' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDiamond_C_public

#check Solidity.Frontend.C3Exactness.graphDiamond_constructor_subsequence
/-- info: 'Solidity.Frontend.C3Exactness.graphDiamond_constructor_subsequence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDiamond_constructor_subsequence

#check Solidity.Frontend.C3Exactness.graphInterfaceUnit
/-- info: 'Solidity.Frontend.C3Exactness.graphInterfaceUnit' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphInterfaceUnit

#check Solidity.Frontend.C3Exactness.graphInterfaceDiamond
/-- info: 'Solidity.Frontend.C3Exactness.graphInterfaceDiamond' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphInterfaceDiamond

#check Solidity.Frontend.C3Exactness.graphInterfaceDiamond_admitted
/-- info: 'Solidity.Frontend.C3Exactness.graphInterfaceDiamond_admitted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphInterfaceDiamond_admitted

#check Solidity.Frontend.C3Exactness.graphInterfaceDiamond_public
/-- info: 'Solidity.Frontend.C3Exactness.graphInterfaceDiamond_public' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphInterfaceDiamond_public

#check Solidity.Frontend.C3Exactness.graphInterfaceDiamond_identities
/-- info: 'Solidity.Frontend.C3Exactness.graphInterfaceDiamond_identities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphInterfaceDiamond_identities

#check Solidity.Frontend.C3Exactness.graphMixed
/-- info: 'Solidity.Frontend.C3Exactness.graphMixed' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphMixed

#check Solidity.Frontend.C3Exactness.graphMixed_admitted
/-- info: 'Solidity.Frontend.C3Exactness.graphMixed_admitted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphMixed_admitted

#check Solidity.Frontend.C3Exactness.graphMixed_public
/-- info: 'Solidity.Frontend.C3Exactness.graphMixed_public' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphMixed_public

#check Solidity.Frontend.C3Exactness.graphBadInterface
/-- info: 'Solidity.Frontend.C3Exactness.graphBadInterface' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphBadInterface

#check Solidity.Frontend.C3Exactness.graphBadInterface_not_admitted
/-- info: 'Solidity.Frontend.C3Exactness.graphBadInterface_not_admitted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphBadInterface_not_admitted

#check Solidity.Frontend.C3Exactness.graphBadInterface_merge_only
/-- info: 'Solidity.Frontend.C3Exactness.graphBadInterface_merge_only' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphBadInterface_merge_only

#check Solidity.Frontend.C3Exactness.graphDuplicate
/-- info: 'Solidity.Frontend.C3Exactness.graphDuplicate' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDuplicate

#check Solidity.Frontend.C3Exactness.graphDuplicate_first_selected
/-- info: 'Solidity.Frontend.C3Exactness.graphDuplicate_first_selected' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDuplicate_first_selected

#check Solidity.Frontend.C3Exactness.graphDuplicate_public_first
/-- info: 'Solidity.Frontend.C3Exactness.graphDuplicate_public_first' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDuplicate_public_first

#check Solidity.Frontend.C3Exactness.graphDuplicate_unselected
/-- info: 'Solidity.Frontend.C3Exactness.graphDuplicate_unselected' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDuplicate_unselected

#check Solidity.Frontend.C3Exactness.graphDuplicate_clashes
/-- info: 'Solidity.Frontend.C3Exactness.graphDuplicate_clashes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphDuplicate_clashes

#check Solidity.Frontend.C3Exactness.graphSettings
/-- info: 'Solidity.Frontend.C3Exactness.graphSettings' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphSettings

#check Solidity.Frontend.C3Exactness.graphResolution
/-- info: 'Solidity.Frontend.C3Exactness.graphResolution' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphResolution

#check Solidity.Frontend.C3Exactness.graphResolution_resolves
/-- info: 'Solidity.Frontend.C3Exactness.graphResolution_resolves' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphResolution_resolves

#check Solidity.Frontend.C3Exactness.graphResolution_identities
/-- info: 'Solidity.Frontend.C3Exactness.graphResolution_identities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphResolution_identities

#check Solidity.Frontend.C3Exactness.nameAt
/-- info: 'Solidity.Frontend.C3Exactness.nameAt' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.nameAt

#check Solidity.Frontend.C3Exactness.GoodId
/-- info: 'Solidity.Frontend.C3Exactness.GoodId' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.GoodId

#check Solidity.Frontend.C3Exactness.nameAt_rank
/-- info: 'Solidity.Frontend.C3Exactness.nameAt_rank' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.nameAt_rank

#check Solidity.Frontend.C3Exactness.rank_good
/-- info: 'Solidity.Frontend.C3Exactness.rank_good' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.rank_good

#check Solidity.Frontend.C3Exactness.rank_injects
/-- info: 'Solidity.Frontend.C3Exactness.rank_injects' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.rank_injects

#check Solidity.Frontend.C3Exactness.nameAt_injects
/-- info: 'Solidity.Frontend.C3Exactness.nameAt_injects' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.nameAt_injects

#check Solidity.Frontend.C3Exactness.merge_input_known
/-- info: 'Solidity.Frontend.C3Exactness.merge_input_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.merge_input_known

#check Solidity.Frontend.C3Exactness.IdentityLin
/-- info: 'Solidity.Frontend.C3Exactness.IdentityLin' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.IdentityLin

#check Solidity.Frontend.C3Exactness.ExactLin.identities
/-- info: 'Solidity.Frontend.C3Exactness.ExactLin.identities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ExactLin.identities

#check Solidity.Frontend.C3Exactness.identity_input_good
/-- info: 'Solidity.Frontend.C3Exactness.identity_input_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.identity_input_good

#check Solidity.Frontend.C3Exactness.IdentityLin.known
/-- info: 'Solidity.Frontend.C3Exactness.IdentityLin.known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.IdentityLin.known

#check Solidity.Frontend.C3Exactness.decode_bases
/-- info: 'Solidity.Frontend.C3Exactness.decode_bases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.decode_bases

#check Solidity.Frontend.C3Exactness.IdentityLin.decode
/-- info: 'Solidity.Frontend.C3Exactness.IdentityLin.decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.IdentityLin.decode

#check Solidity.Frontend.C3Exactness.IdentityLin.roundtrip
/-- info: 'Solidity.Frontend.C3Exactness.IdentityLin.roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.IdentityLin.roundtrip

#check Solidity.Frontend.C3Exactness.IdentityLin.unique
/-- info: 'Solidity.Frontend.C3Exactness.IdentityLin.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.IdentityLin.unique

#check Solidity.Frontend.C3Exactness.IdentityLin.nodup
/-- info: 'Solidity.Frontend.C3Exactness.IdentityLin.nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.IdentityLin.nodup

#check Solidity.Frontend.C3Exactness.IdentityLin.graph_nodes
/-- info: 'Solidity.Frontend.C3Exactness.IdentityLin.graph_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.IdentityLin.graph_nodes

#check Solidity.Frontend.C3Exactness.linearize_identity_iff
/-- info: 'Solidity.Frontend.C3Exactness.linearize_identity_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.linearize_identity_iff

#check Solidity.Frontend.C3Exactness.linearize_selected_identity_iff
/-- info: 'Solidity.Frontend.C3Exactness.linearize_selected_identity_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.linearize_selected_identity_iff

#check Solidity.Frontend.C3Exactness.collect_root_scope
/-- info: 'Solidity.Frontend.C3Exactness.collect_root_scope' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.collect_root_scope

#check Solidity.Frontend.C3Exactness.unit_decl_selected
/-- info: 'Solidity.Frontend.C3Exactness.unit_decl_selected' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.unit_decl_selected

#check Solidity.Frontend.C3Exactness.unit_contract_selected
/-- info: 'Solidity.Frontend.C3Exactness.unit_contract_selected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.unit_contract_selected

#check Solidity.Frontend.C3Exactness.unit_identity_iff
/-- info: 'Solidity.Frontend.C3Exactness.unit_identity_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.unit_identity_iff

#check Solidity.Frontend.C3Exactness.resolved_identity_iff
/-- info: 'Solidity.Frontend.C3Exactness.resolved_identity_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.resolved_identity_iff

#check Solidity.Frontend.C3Exactness.IdentityLin.mk
/-- info: 'Solidity.Frontend.C3Exactness.IdentityLin.mk' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.IdentityLin.mk

#check Solidity.Frontend.C3Exactness.ExactLin
/-- info: 'Solidity.Frontend.C3Exactness.ExactLin' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ExactLin

#check Solidity.Frontend.C3Exactness.paired_get
/-- info: 'Solidity.Frontend.C3Exactness.paired_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.paired_get

#check Solidity.Frontend.C3Exactness.mapM_complete
/-- info: 'Solidity.Frontend.C3Exactness.mapM_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.mapM_complete

#check Solidity.Frontend.C3Exactness.linearizeF_exact_sound
/-- info: 'Solidity.Frontend.C3Exactness.linearizeF_exact_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.linearizeF_exact_sound

#check Solidity.Frontend.C3Exactness.ExactLin.unique
/-- info: 'Solidity.Frontend.C3Exactness.ExactLin.unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ExactLin.unique

#check Solidity.Frontend.C3Exactness.trace_rank_lt
/-- info: 'Solidity.Frontend.C3Exactness.trace_rank_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.trace_rank_lt

#check Solidity.Frontend.C3Exactness.ExactLin.rank_bound
/-- info: 'Solidity.Frontend.C3Exactness.ExactLin.rank_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ExactLin.rank_bound

#check Solidity.Frontend.C3Exactness.ExactLin.tail_rank
/-- info: 'Solidity.Frontend.C3Exactness.ExactLin.tail_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ExactLin.tail_rank

#check Solidity.Frontend.C3Exactness.ExactLin.tail_nodup
/-- info: 'Solidity.Frontend.C3Exactness.ExactLin.tail_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ExactLin.tail_nodup

#check Solidity.Frontend.C3Exactness.ExactLin.tail_length
/-- info: 'Solidity.Frontend.C3Exactness.ExactLin.tail_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ExactLin.tail_length

#check Solidity.Frontend.C3Exactness.ExactLin.nodup
/-- info: 'Solidity.Frontend.C3Exactness.ExactLin.nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ExactLin.nodup

#check Solidity.Frontend.C3Exactness.ExactLin.complete
/-- info: 'Solidity.Frontend.C3Exactness.ExactLin.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ExactLin.complete

#check Solidity.Frontend.C3Exactness.linearize_exact_iff
/-- info: 'Solidity.Frontend.C3Exactness.linearize_exact_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.linearize_exact_iff

#check Solidity.Frontend.C3Exactness.linearize_none_iff
/-- info: 'Solidity.Frontend.C3Exactness.linearize_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.linearize_none_iff

#check Solidity.Frontend.C3Exactness.linearizeF_unique
/-- info: 'Solidity.Frontend.C3Exactness.linearizeF_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.linearizeF_unique

#check Solidity.Frontend.C3Exactness.Reaches
/-- info: 'Solidity.Frontend.C3Exactness.Reaches' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Reaches

#check Solidity.Frontend.C3Exactness.ExactLin.mem_iff
/-- info: 'Solidity.Frontend.C3Exactness.ExactLin.mem_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ExactLin.mem_iff

#check Solidity.Frontend.C3Exactness.ExactLin.direct_order
/-- info: 'Solidity.Frontend.C3Exactness.ExactLin.direct_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ExactLin.direct_order

#check Solidity.Frontend.C3Exactness.ExactLin.monotone
/-- info: 'Solidity.Frontend.C3Exactness.ExactLin.monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ExactLin.monotone

#check Solidity.Frontend.C3Exactness.exact_ctorOrder
/-- info: 'Solidity.Frontend.C3Exactness.exact_ctorOrder' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.exact_ctorOrder

#check Solidity.Frontend.C3Exactness.ctor_direct_order
/-- info: 'Solidity.Frontend.C3Exactness.ctor_direct_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ctor_direct_order

#check Solidity.Frontend.C3Exactness.ctor_monotone
/-- info: 'Solidity.Frontend.C3Exactness.ctor_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ctor_monotone

#check Solidity.Frontend.C3Exactness.ctor_nodup
/-- info: 'Solidity.Frontend.C3Exactness.ctor_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ctor_nodup

#check Solidity.Frontend.C3Exactness.linearizeF_self_cycle
/-- info: 'Solidity.Frontend.C3Exactness.linearizeF_self_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.linearizeF_self_cycle

#check Solidity.Frontend.C3Exactness.GraphBlocked
/-- info: 'Solidity.Frontend.C3Exactness.GraphBlocked' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.GraphBlocked

#check Solidity.Frontend.C3Exactness.mapM_none
/-- info: 'Solidity.Frontend.C3Exactness.mapM_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.mapM_none

#check Solidity.Frontend.C3Exactness.GraphBlocked.not_exact
/-- info: 'Solidity.Frontend.C3Exactness.GraphBlocked.not_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.GraphBlocked.not_exact

#check Solidity.Frontend.C3Exactness.graph_trace_or_blocked
/-- info: 'Solidity.Frontend.C3Exactness.graph_trace_or_blocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graph_trace_or_blocked

#check Solidity.Frontend.C3Exactness.linearize_none_iff_blocked
/-- info: 'Solidity.Frontend.C3Exactness.linearize_none_iff_blocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.linearize_none_iff_blocked

#check Solidity.Frontend.C3Exactness.GraphBlocked.linearizeF_none
/-- info: 'Solidity.Frontend.C3Exactness.GraphBlocked.linearizeF_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.GraphBlocked.linearizeF_none

#check Solidity.Frontend.C3Exactness.CyclePath
/-- info: 'Solidity.Frontend.C3Exactness.CyclePath' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.CyclePath

#check Solidity.Frontend.C3Exactness.CyclePath.rank_lt
/-- info: 'Solidity.Frontend.C3Exactness.CyclePath.rank_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.CyclePath.rank_lt

#check Solidity.Frontend.C3Exactness.ExactLin.base_length
/-- info: 'Solidity.Frontend.C3Exactness.ExactLin.base_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ExactLin.base_length

#check Solidity.Frontend.C3Exactness.CyclePath.descendant
/-- info: 'Solidity.Frontend.C3Exactness.CyclePath.descendant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.CyclePath.descendant

#check Solidity.Frontend.C3Exactness.CyclePath.not_exact
/-- info: 'Solidity.Frontend.C3Exactness.CyclePath.not_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.CyclePath.not_exact

#check Solidity.Frontend.C3Exactness.CyclePath.linearizeF_none
/-- info: 'Solidity.Frontend.C3Exactness.CyclePath.linearizeF_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.CyclePath.linearizeF_none

#check Solidity.Frontend.C3Exactness.ExactLin.mk
/-- info: 'Solidity.Frontend.C3Exactness.ExactLin.mk' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.ExactLin.mk

#check Solidity.Frontend.C3Exactness.Reaches.refl
/-- info: 'Solidity.Frontend.C3Exactness.Reaches.refl' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Reaches.refl

#check Solidity.Frontend.C3Exactness.Reaches.step
/-- info: 'Solidity.Frontend.C3Exactness.Reaches.step' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Reaches.step

#check Solidity.Frontend.C3Exactness.GraphBlocked.merge
/-- info: 'Solidity.Frontend.C3Exactness.GraphBlocked.merge' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.GraphBlocked.merge

#check Solidity.Frontend.C3Exactness.GraphBlocked.base
/-- info: 'Solidity.Frontend.C3Exactness.GraphBlocked.base' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.GraphBlocked.base

#check Solidity.Frontend.C3Exactness.CyclePath.direct
/-- info: 'Solidity.Frontend.C3Exactness.CyclePath.direct' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.CyclePath.direct

#check Solidity.Frontend.C3Exactness.CyclePath.step
/-- info: 'Solidity.Frontend.C3Exactness.CyclePath.step' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.CyclePath.step

#check Solidity.Frontend.C3Exactness.InjectsOn
/-- info: 'Solidity.Frontend.C3Exactness.InjectsOn' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.InjectsOn

#check Solidity.Frontend.C3Exactness.mem_map_reflect
/-- info: 'Solidity.Frontend.C3Exactness.mem_map_reflect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.mem_map_reflect

#check Solidity.Frontend.C3Exactness.admissible_map
/-- info: 'Solidity.Frontend.C3Exactness.admissible_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.admissible_map

#check Solidity.Frontend.C3Exactness.active_map
/-- info: 'Solidity.Frontend.C3Exactness.active_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.active_map

#check Solidity.Frontend.C3Exactness.filter_map_ne
/-- info: 'Solidity.Frontend.C3Exactness.filter_map_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.filter_map_ne

#check Solidity.Frontend.C3Exactness.residual_map
/-- info: 'Solidity.Frontend.C3Exactness.residual_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.residual_map

#check Solidity.Frontend.C3Exactness.findSome_congr
/-- info: 'Solidity.Frontend.C3Exactness.findSome_congr' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.findSome_congr

#check Solidity.Frontend.C3Exactness.findSome_result_map
/-- info: 'Solidity.Frontend.C3Exactness.findSome_result_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.findSome_result_map

#check Solidity.Frontend.C3Exactness.first_map
/-- info: 'Solidity.Frontend.C3Exactness.first_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.first_map

#check Solidity.Frontend.C3Exactness.Trace.rename
/-- info: 'Solidity.Frontend.C3Exactness.Trace.rename' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Trace.rename

#check Solidity.Frontend.C3Exactness.Stuck.rename
/-- info: 'Solidity.Frontend.C3Exactness.Stuck.rename' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Stuck.rename

#check Solidity.Frontend.C3Exactness.rename_exists_iff
/-- info: 'Solidity.Frontend.C3Exactness.rename_exists_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.rename_exists_iff

#check Solidity.Frontend.C3Exactness.active
/-- info: 'Solidity.Frontend.C3Exactness.active' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.active

#check Solidity.Frontend.C3Exactness.admissible
/-- info: 'Solidity.Frontend.C3Exactness.admissible' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.admissible

#check Solidity.Frontend.C3Exactness.first
/-- info: 'Solidity.Frontend.C3Exactness.first' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.first

#check Solidity.Frontend.C3Exactness.residual
/-- info: 'Solidity.Frontend.C3Exactness.residual' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.residual

#check Solidity.Frontend.C3Exactness.Trace
/-- info: 'Solidity.Frontend.C3Exactness.Trace' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Trace

#check Solidity.Frontend.C3Exactness.Obstruction
/-- info: 'Solidity.Frontend.C3Exactness.Obstruction' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Obstruction

#check Solidity.Frontend.C3Exactness.Stuck
/-- info: 'Solidity.Frontend.C3Exactness.Stuck' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Stuck

#check Solidity.Frontend.C3Exactness.first_empty
/-- info: 'Solidity.Frontend.C3Exactness.first_empty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.first_empty

#check Solidity.Frontend.C3Exactness.merge_succ
/-- info: 'Solidity.Frontend.C3Exactness.merge_succ' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.merge_succ

#check Solidity.Frontend.C3Exactness.merge_sound
/-- info: 'Solidity.Frontend.C3Exactness.merge_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.merge_sound

#check Solidity.Frontend.C3Exactness.Trace.complete
/-- info: 'Solidity.Frontend.C3Exactness.Trace.complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Trace.complete

#check Solidity.Frontend.C3Exactness.Trace.unique
/-- info: 'Solidity.Frontend.C3Exactness.Trace.unique' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Trace.unique

#check Solidity.Frontend.C3Exactness.merge_fuel
/-- info: 'Solidity.Frontend.C3Exactness.merge_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.merge_fuel

#check Solidity.Frontend.C3Exactness.merge_iff
/-- info: 'Solidity.Frontend.C3Exactness.merge_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.merge_iff

#check Solidity.Frontend.C3Exactness.admissible_iff
/-- info: 'Solidity.Frontend.C3Exactness.admissible_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.admissible_iff

#check Solidity.Frontend.C3Exactness.first_iff
/-- info: 'Solidity.Frontend.C3Exactness.first_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.first_iff

#check Solidity.Frontend.C3Exactness.first_mem
/-- info: 'Solidity.Frontend.C3Exactness.first_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.first_mem

#check Solidity.Frontend.C3Exactness.flatten_active
/-- info: 'Solidity.Frontend.C3Exactness.flatten_active' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.flatten_active

#check Solidity.Frontend.C3Exactness.flatten_residual
/-- info: 'Solidity.Frontend.C3Exactness.flatten_residual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.flatten_residual

#check Solidity.Frontend.C3Exactness.residual_decreases
/-- info: 'Solidity.Frontend.C3Exactness.residual_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.residual_decreases

#check Solidity.Frontend.C3Exactness.Trace.length_le
/-- info: 'Solidity.Frontend.C3Exactness.Trace.length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Trace.length_le

#check Solidity.Frontend.C3Exactness.trace_or_stuck
/-- info: 'Solidity.Frontend.C3Exactness.trace_or_stuck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.trace_or_stuck

#check Solidity.Frontend.C3Exactness.Stuck.not_trace
/-- info: 'Solidity.Frontend.C3Exactness.Stuck.not_trace' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Stuck.not_trace

#check Solidity.Frontend.C3Exactness.Stuck.merge_none
/-- info: 'Solidity.Frontend.C3Exactness.Stuck.merge_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Stuck.merge_none

#check Solidity.Frontend.C3Exactness.merge_none_iff
/-- info: 'Solidity.Frontend.C3Exactness.merge_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.merge_none_iff

#check Solidity.Frontend.C3Exactness.fuelBound
/-- info: 'Solidity.Frontend.C3Exactness.fuelBound' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.fuelBound

#check Solidity.Frontend.C3Exactness.merge_bound_none_iff
/-- info: 'Solidity.Frontend.C3Exactness.merge_bound_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.merge_bound_none_iff

#check Solidity.Frontend.C3Exactness.merge_bound_iff
/-- info: 'Solidity.Frontend.C3Exactness.merge_bound_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.merge_bound_iff

#check Solidity.Frontend.C3Exactness.Trace.mem_iff
/-- info: 'Solidity.Frontend.C3Exactness.Trace.mem_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Trace.mem_iff

#check Solidity.Frontend.C3Exactness.Trace.nodup
/-- info: 'Solidity.Frontend.C3Exactness.Trace.nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Trace.nodup

#check Solidity.Frontend.C3Exactness.first_head
/-- info: 'Solidity.Frontend.C3Exactness.first_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.first_head

#check Solidity.Frontend.C3Exactness.filter_head
/-- info: 'Solidity.Frontend.C3Exactness.filter_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.filter_head

#check Solidity.Frontend.C3Exactness.Trace.local_order
/-- info: 'Solidity.Frontend.C3Exactness.Trace.local_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Trace.local_order

#check Solidity.Frontend.C3Exactness.first_none_iff
/-- info: 'Solidity.Frontend.C3Exactness.first_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.first_none_iff

#check Solidity.Frontend.C3Exactness.obstruction_iff
/-- info: 'Solidity.Frontend.C3Exactness.obstruction_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.obstruction_iff

#check Solidity.Frontend.C3Exactness.Trace.done
/-- info: 'Solidity.Frontend.C3Exactness.Trace.done' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Trace.done

#check Solidity.Frontend.C3Exactness.Trace.step
/-- info: 'Solidity.Frontend.C3Exactness.Trace.step' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Trace.step

#check Solidity.Frontend.C3Exactness.Stuck.here
/-- info: 'Solidity.Frontend.C3Exactness.Stuck.here' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Stuck.here

#check Solidity.Frontend.C3Exactness.Stuck.step
/-- info: 'Solidity.Frontend.C3Exactness.Stuck.step' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Stuck.step

/-! Closed case witnesses and required public theorem interfaces. -/
#check (Solidity.Frontend.C3Exactness.Controls.empty_trace : Trace ([] : List (List String)) [])
#check (Solidity.Frontend.C3Exactness.Controls.identity_trace : Trace ([[1], [2, 1]] : List (List Nat)) [2, 1])
#check (Solidity.Frontend.C3Exactness.Controls.independent_heads : Trace [["a"], ["b"]] ["a", "b"])
#check (Solidity.Frontend.C3Exactness.Controls.diamond_merge : Trace [["B", "A"], ["C", "A"], ["B", "C"]] ["B", "C", "A"])
#check (Solidity.Frontend.C3Exactness.Controls.cycle_stuck : Stuck [["a", "b"], ["b", "a"]])
#check (Solidity.Frontend.C3Exactness.graphBad_merge_stuck : Stuck [["Y", "A", "B"], ["X", "B", "A"], ["Y", "X"]])
#check (Solidity.Frontend.C3Exactness.graphDiamond_exact : ExactLin graphDiamond.env "D" ["D", "C", "B", "A"])
#check (Solidity.Frontend.C3Exactness.graphShared_exact : ExactLin graphShared.env "F" ["F", "E", "D", "C", "B", "A"])
#check (Solidity.Frontend.C3Exactness.graphDiamond_refl : Reaches graphDiamond.env "D" "D")
#check (Solidity.Frontend.C3Exactness.graphDiamond_reaches : Reaches graphDiamond.env "D" "A")
#check (Solidity.Frontend.C3Exactness.graphBad_certificate : GraphBlocked graphBad.env "Z")
#check (Solidity.Frontend.C3Exactness.graphBad_inherited_certificate : GraphBlocked graphBad.env "W")
#check (Solidity.Frontend.C3Exactness.graphSelfCycle_path : CyclePath graphSelfCycle.env "S" "S")
#check (Solidity.Frontend.C3Exactness.graphMutualCycle_path : CyclePath graphMutualCycle.env "P" "P")
#check (Solidity.Frontend.C3Exactness.graphDiamond_identities : IdentityLin graphDiamond.env 3 [3, 2, 1, 0])
#check (Solidity.Frontend.C3Exactness.graphInterfaceDiamond_identities : IdentityLin graphInterfaceDiamond.env 3 [3, 2, 1, 0])
#check (Solidity.Frontend.C3Exactness.graphResolution_identities : IdentityLin graphResolution.env 3 [3, 2, 1, 0])
#check (Solidity.Frontend.C3Exactness.merge_iff : ∀ {n : Nat} {ls : List (List String)} {out : List String}, Env.merge n ls = some out ↔ Trace ls out ∧ out.length < n)
#check (Solidity.Frontend.C3Exactness.Trace.unique : ∀ {α : Type} [DecidableEq α] {ls : List (List α)} {a b : List α}, Trace ls a → Trace ls b → a = b)
#check (Solidity.Frontend.C3Exactness.linearize_exact_iff : ∀ {E : Env}, E.basesOK = true → ∀ (c : String) (L : List String), E.linearize c = some L ↔ ExactLin E c L)
#check (Solidity.Frontend.C3Exactness.linearize_none_iff_blocked : ∀ {E : Env}, E.basesOK = true → ∀ c : String, E.linearize c = none ↔ GraphBlocked E c)
#check (Solidity.Frontend.C3Exactness.CyclePath.linearizeF_none : ∀ {E : Env} {c : String}, CyclePath E c c → ∀ n : Nat, E.linearizeF n c = none)
#check (Solidity.Frontend.C3Exactness.IdentityLin.unique : ∀ {E : Env} {i : Nat} {a b : List Nat}, IdentityLin E i a → IdentityLin E i b → E.basesOK = true → a = b)
#check (Solidity.Frontend.C3Exactness.unit_identity_iff : ∀ (u : Syn .unit), u.env.basesOK = true → ∀ c : String, c ∈ u.env.contractNames → ∀ I : List Nat, (u.env.linearize c).map (List.map (rank u.env)) = some I ↔ IdentityLin u.env (rank u.env c) I)
#check (Solidity.Frontend.C3Exactness.resolved_identity_iff : ∀ {s : Settings} {u : Syn .unit} {r : Resolution}, Resolves' s u r → r.env.basesOK = true → ∀ c : String, c ∈ r.env.contractNames → ∀ I : List Nat, (r.env.linearize c).map (List.map (rank r.env)) = some I ↔ IdentityLin r.env (rank r.env c) I)
#check (Solidity.Frontend.C3Exactness.ctor_monotone : ∀ {E : Env} {c b : String} {L Lb : List String}, E.linearize c = some L → b ∈ E.bases c → E.linearize b = some Lb → (E.ctorOrder b).Sublist (E.ctorOrder c).dropLast)
#check (Solidity.Frontend.C3Exactness.ctor_nodup : ∀ {E : Env} {c : String} {L : List String}, E.basesOK = true → E.linearize c = some L → (E.ctorOrder c).Nodup)

#check (show graphUnit [] = Syn.unit Syn.nil from rfl)
#check (show graphSpecs ["A"] = Syn.cons (Syn.inherit ⟨"A", []⟩ Syn.none) Syn.nil from rfl)
#check (show graphUnit [("A", [])] = Syn.unit (Syn.cons (Syn.contract false "A" Syn.none Syn.nil Syn.nil) Syn.nil) from rfl)
#check (show graphInterfaceUnit [("I", [])] = Syn.unit (Syn.cons (Syn.interface "I" Syn.nil Syn.nil) Syn.nil) from rfl)

-- Typed interfaces paired with exact external-source fixture observations.
#check (Solidity.Frontend.C3Exactness.graphDiamond_public : graphDiamond.env.linearize "D" = some ["D", "C", "B", "A"])
#check (Solidity.Frontend.C3Exactness.graphDiamond_constructors : graphDiamond.env.ctorOrder "D" = ["A", "B", "C", "D"])
#check (Solidity.Frontend.C3Exactness.graphShared_public : graphShared.env.linearize "F" = some ["F", "E", "D", "C", "B", "A"])
#check (Solidity.Frontend.C3Exactness.graphShared_constructors : graphShared.env.ctorOrder "F" = ["A", "B", "C", "D", "E", "F"])
#check (Solidity.Frontend.C3Exactness.graphRedundant_public : graphRedundant.env.linearize "C" = some ["C", "B", "A"])
#check (Solidity.Frontend.C3Exactness.graphRedundant_constructors : graphRedundant.env.ctorOrder "C" = ["A", "B", "C"])
#check (Solidity.Frontend.C3Exactness.graphInterfaceDiamond_public : graphInterfaceDiamond.env.linearize "ID" = some ["ID", "IC", "IB", "IA"])
#check (Solidity.Frontend.C3Exactness.graphMixed_public : graphMixed.env.linearize "C" = some ["C", "IB", "IA"])
#check (Solidity.Frontend.C3Exactness.graphBad_public_refused : graphBad.env.linearize "Z" = none)
#check (Solidity.Frontend.C3Exactness.graphBad_inherited_all_fuel : ∀ n : Nat, graphBad.env.linearizeF n "W" = none)
#check (Solidity.Frontend.C3Exactness.graphSelfCycle_all_fuel : ∀ n : Nat, graphSelfCycle.env.linearizeF n "S" = none)
#check (Solidity.Frontend.C3Exactness.graphMutualCycle_all_fuel : ∀ n : Nat, graphMutualCycle.env.linearizeF n "P" = none)
#check (Solidity.Frontend.C3Exactness.graphBadInterface_not_admitted : graphBadInterface.env.basesOK = false)

-- New order-obstruction declaration and actual axiom discovery.
#check Solidity.Frontend.C3Exactness.CommonOrder
/-- info: 'Solidity.Frontend.C3Exactness.CommonOrder' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.CommonOrder
#check Solidity.Frontend.C3Exactness.Controls.alternative_common_order
/-- info: 'Solidity.Frontend.C3Exactness.Controls.alternative_common_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.alternative_common_order
#check Solidity.Frontend.C3Exactness.Controls.alternative_not_trace
/-- info: 'Solidity.Frontend.C3Exactness.Controls.alternative_not_trace' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.alternative_not_trace
#check Solidity.Frontend.C3Exactness.Controls.cycle_not_common_order
/-- info: 'Solidity.Frontend.C3Exactness.Controls.cycle_not_common_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Controls.cycle_not_common_order
#check Solidity.Frontend.C3Exactness.Obstruction.not_common_order
/-- info: 'Solidity.Frontend.C3Exactness.Obstruction.not_common_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Obstruction.not_common_order
#check Solidity.Frontend.C3Exactness.Stuck.not_common_order
/-- info: 'Solidity.Frontend.C3Exactness.Stuck.not_common_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Stuck.not_common_order
#check Solidity.Frontend.C3Exactness.Trace.common_order
/-- info: 'Solidity.Frontend.C3Exactness.Trace.common_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.Trace.common_order
#check Solidity.Frontend.C3Exactness.graphBad_identity_no_order
/-- info: 'Solidity.Frontend.C3Exactness.graphBad_identity_no_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphBad_identity_no_order
#check Solidity.Frontend.C3Exactness.graphBad_merge_no_order
/-- info: 'Solidity.Frontend.C3Exactness.graphBad_merge_no_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.graphBad_merge_no_order
#check Solidity.Frontend.C3Exactness.merge_bound_exists_iff_common_order
/-- info: 'Solidity.Frontend.C3Exactness.merge_bound_exists_iff_common_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.merge_bound_exists_iff_common_order
#check Solidity.Frontend.C3Exactness.merge_bound_none_iff_no_common_order
/-- info: 'Solidity.Frontend.C3Exactness.merge_bound_none_iff_no_common_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.merge_bound_none_iff_no_common_order
#check Solidity.Frontend.C3Exactness.merge_none_iff_order_or_fuel
/-- info: 'Solidity.Frontend.C3Exactness.merge_none_iff_order_or_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.merge_none_iff_order_or_fuel
#check Solidity.Frontend.C3Exactness.stuck_iff_no_common_order
/-- info: 'Solidity.Frontend.C3Exactness.stuck_iff_no_common_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.stuck_iff_no_common_order
#check Solidity.Frontend.C3Exactness.trace_exists_iff_common_order
/-- info: 'Solidity.Frontend.C3Exactness.trace_exists_iff_common_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.C3Exactness.trace_exists_iff_common_order

#check (show (fun {α : Type} (ls : List (List α)) (out : List α) => CommonOrder ls out) = (fun {α : Type} (ls : List (List α)) (out : List α) => out.Nodup ∧ ∀ l ∈ ls, l.Sublist out) from rfl)
#check (Solidity.Frontend.C3Exactness.Controls.alternative_common_order : CommonOrder ([[0], [1]] : List (List Nat)) [1, 0])
#check (Solidity.Frontend.C3Exactness.Controls.alternative_not_trace : ¬ Trace ([[0], [1]] : List (List Nat)) [1, 0])
#check (Solidity.Frontend.C3Exactness.graphBad_merge_no_order : ∀ out, ¬ CommonOrder [["Y", "A", "B"], ["X", "B", "A"], ["Y", "X"]] out)
#check (Solidity.Frontend.C3Exactness.graphBad_identity_no_order : ∀ out, ¬ CommonOrder ([[3, 0, 1], [2, 1, 0], [3, 2]] : List (List Nat)) out)
#check (Solidity.Frontend.C3Exactness.Trace.common_order : ∀ {α : Type} [DecidableEq α] {ls : List (List α)} {out : List α}, Trace ls out → CommonOrder ls out)
#check (Solidity.Frontend.C3Exactness.Obstruction.not_common_order : ∀ {α : Type} [DecidableEq α] {ls : List (List α)}, Obstruction ls → ∀ out, ¬ CommonOrder ls out)
#check (Solidity.Frontend.C3Exactness.Stuck.not_common_order : ∀ {α : Type} [DecidableEq α] {ls : List (List α)}, Stuck ls → ∀ out, ¬ CommonOrder ls out)
#check (Solidity.Frontend.C3Exactness.stuck_iff_no_common_order : ∀ {α : Type} [DecidableEq α] (ls : List (List α)), Stuck ls ↔ ¬ ∃ out, CommonOrder ls out)
#check (Solidity.Frontend.C3Exactness.trace_exists_iff_common_order : ∀ {α : Type} [DecidableEq α] (ls : List (List α)), (∃ out, Trace ls out) ↔ ∃ out, CommonOrder ls out)
#check (Solidity.Frontend.C3Exactness.merge_bound_none_iff_no_common_order : ∀ ls : List (List String), Env.merge (fuelBound ls) ls = none ↔ ¬ ∃ out, CommonOrder ls out)
#check (Solidity.Frontend.C3Exactness.merge_bound_exists_iff_common_order : ∀ ls : List (List String), (∃ out, Env.merge (fuelBound ls) ls = some out) ↔ ∃ out, CommonOrder ls out)
#check (Solidity.Frontend.C3Exactness.merge_none_iff_order_or_fuel : ∀ (n : Nat) (ls : List (List String)), Env.merge n ls = none ↔ (¬ ∃ out, CommonOrder ls out) ∨ ∃ out, Trace ls out ∧ n ≤ out.length)
#check (Solidity.Frontend.C3Exactness.Controls.cycle_not_common_order : ∀ {α : Type} [DecidableEq α] (a b : α), ∀ out, ¬ CommonOrder [[a, b], [b, a]] out)
