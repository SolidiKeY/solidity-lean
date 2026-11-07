import Solidity.Frontend.OverrideValidation.Memoized

open Solidity.Frontend.OverrideValidation

/-- info: 'Solidity.Frontend.OverrideValidation.visibilityAllowedB_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms visibilityAllowedB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.mutabilityAllowedB_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mutabilityAllowedB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.signatureConditionB_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms signatureConditionB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.virtualB_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms virtualB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.pairTypesB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pairTypesB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.compatibleB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compatibleB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.syntax_equality_reflect' depends on axioms: [propext] -/
#guard_msgs in
#print axioms syntax_equality_reflect
/-- info: 'Solidity.Frontend.OverrideValidation.declaration_equality_reflect' depends on axioms: [propext] -/
#guard_msgs in
#print axioms declaration_equality_reflect
/-- info: 'Solidity.Frontend.OverrideValidation.extractionB_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms extractionB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.complete_collected_member' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms complete_collected_member
/-- info: 'Solidity.Frontend.OverrideValidation.collected_member_position' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms collected_member_position
/-- info: 'Solidity.Frontend.OverrideValidation.mem_nodes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mem_nodes
/-- info: 'Solidity.Frontend.OverrideValidation.any_nodes_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms any_nodes_iff
/-- info: 'Solidity.Frontend.OverrideValidation.refersB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refersB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.baseEdgeB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms baseEdgeB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.ownB_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ownB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.paramsB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms paramsB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.sameSlotB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sameSlotB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.ownMatchingB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ownMatchingB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.route_rel_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms route_rel_iff
/-- info: 'Solidity.Frontend.OverrideValidation.routeB_rel_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms routeB_rel_iff
/-- info: 'Solidity.Frontend.OverrideValidation.shadowStepB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shadowStepB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.frontierB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frontierB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.mem_inherited_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_inherited_iff
/-- info: 'Solidity.Frontend.OverrideValidation.selected_in_env' depends on axioms: [propext] -/
#guard_msgs in
#print axioms selected_in_env
/-- info: 'Solidity.Frontend.OverrideValidation.same_node_same_decl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms same_node_same_decl
/-- info: 'Solidity.Frontend.OverrideValidation.distinct_decl_distinct_node' depends on axioms: [propext] -/
#guard_msgs in
#print axioms distinct_decl_distinct_node
/-- info: 'Solidity.Frontend.OverrideValidation.node_lookup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms node_lookup
/-- info: 'Solidity.Frontend.OverrideValidation.selected_lookup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms selected_lookup
/-- info: 'Solidity.Frontend.OverrideValidation.position_identity' does not depend on any axioms -/
#guard_msgs in
#print axioms position_identity
/-- info: 'Solidity.Frontend.OverrideValidation.bitTable_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitTable_get
/-- info: 'Solidity.Frontend.OverrideValidation.edgeTable_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms edgeTable_get
/-- info: 'Solidity.Frontend.OverrideValidation.bitTable_get_fun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitTable_get_fun
/-- info: 'Solidity.Frontend.OverrideValidation.memoRetainedTable_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms memoRetainedTable_get
/-- info: 'Solidity.Frontend.OverrideValidation.fastAmbiguityB_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fastAmbiguityB_eq
/-- info: 'Solidity.Frontend.OverrideValidation.fastValidateB_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fastValidateB_eq
/-- info: 'Solidity.Frontend.OverrideValidation.fastValidateB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fastValidateB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.overrideOwnB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms overrideOwnB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.overrideStepB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms overrideStepB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.overrideFrontierB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms overrideFrontierB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.hasBaseB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasBaseB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.hasOverrideBaseB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasOverrideBaseB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.multipleB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms multipleB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.singleInterfaceB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms singleInterfaceB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.listedB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms listedB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.pathsDistinctB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pathsDistinctB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.namedListB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms namedListB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.overrideListsB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms overrideListsB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.crossFamilyB_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms crossFamilyB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.noCrossFamilyB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noCrossFamilyB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.inheritedFamiliesB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inheritedFamiliesB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.namespaceConflictB_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms namespaceConflictB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.memberNamesB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms memberNamesB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.declarationOverridesB_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms declarationOverridesB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.any_fin_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms any_fin_iff
/-- info: 'Solidity.Frontend.OverrideValidation.all_nodes_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms all_nodes_iff
/-- info: 'Solidity.Frontend.OverrideValidation.overrideEdgeB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms overrideEdgeB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.activeB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms activeB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.adjacentB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms adjacentB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.avoidingB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avoidingB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.cutVertexB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cutVertexB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.retainedB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms retainedB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.mem_survivors_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_survivors_iff
/-- info: 'Solidity.Frontend.OverrideValidation.erase_length_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erase_length_lt
/-- info: 'Solidity.Frontend.OverrideValidation.routeB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms routeB_sound
/-- info: 'Solidity.Frontend.OverrideValidation.routeB_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms routeB_complete
/-- info: 'Solidity.Frontend.OverrideValidation.routeB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms routeB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.exposesB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exposesB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.scopeChoice_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scopeChoice_iff
/-- info: 'Solidity.Frontend.OverrideValidation.scopeChoice_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scopeChoice_none_iff
/-- info: 'Solidity.Frontend.OverrideValidation.choose_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choose_iff
/-- info: 'Solidity.Frontend.OverrideValidation.chosen_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chosen_unique
/-- info: 'Solidity.Frontend.OverrideValidation.chosen_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chosen_slot
/-- info: 'Solidity.Frontend.OverrideValidation.hasOwnB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasOwnB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.implementationB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms implementationB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.ambiguityB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ambiguityB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.dispatch_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dispatch_iff
/-- info: 'Solidity.Frontend.OverrideValidation.dispatch_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dispatch_original
/-- info: 'Solidity.Frontend.OverrideValidation.validateB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms validateB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.concrete_implemented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms concrete_implemented
/-- info: 'Solidity.Frontend.OverrideValidation.accepted_no_self_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms accepted_no_self_base
/-- info: 'Solidity.Frontend.OverrideValidation.accepted_owner_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms accepted_owner_identity
/-- info: 'Solidity.Frontend.OverrideValidation.accepted_slot_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms accepted_slot_identity
/-- info: 'Solidity.Frontend.OverrideValidation.certify_isSome_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certify_isSome_iff
/-- info: 'Solidity.Frontend.OverrideValidation.certify_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certify_none_iff
/-- info: 'Solidity.Frontend.OverrideValidation.accepted_collected_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms accepted_collected_member
/-- info: 'Solidity.Frontend.OverrideValidation.bytesSignatureB_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms bytesSignatureB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.fallbackShapeB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fallbackShapeB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.descriptorB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms descriptorB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.getterReturnsB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms getterReturnsB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.attributesOKB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms attributesOKB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.scopeKnownB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scopeKnownB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.graphValidB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graphValidB_iff
/-- info: 'Solidity.Frontend.OverrideValidation.valid_no_self_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms valid_no_self_base
/-- info: 'Solidity.Frontend.OverrideValidation.valid_owner_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms valid_owner_identity
