import Solidity.Backend.StructuredFlow.SourceDispatchControls

/-! Guards axiom growth in the exact Source dispatcher, its coverage laws and operational certificates. -/

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.Compiled.result_eq_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.Compiled.result_eq_core

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.Compiled.code_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.Compiled.code_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.dispatch_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.dispatch_refuses

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.Compiled.output_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.Compiled.output_unique

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.empty_block_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.empty_block_accepts

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.skip_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.skip_refused

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.literal_condition_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.literal_condition_refused

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.ordered_block_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.ordered_block_accepts

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.incompatible_mapping_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.incompatible_mapping_refused

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.captured_flag_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.captured_flag_control

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.contextMap_boolSlot' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.contextMap_boolSlot

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.Compiled.correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.Compiled.correct

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.program_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.program_admitted

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.dispatch_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.dispatch_checked

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.dispatch_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.dispatch_accepts

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.dispatch_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.dispatch_complete

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.dispatch_template_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.dispatch_template_complete

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.dispatch_error_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.dispatch_error_boundary

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.Plan.context_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.Plan.context_same

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.conditional_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.conditional_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.itemSpine_sourceItems' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.itemSpine_sourceItems

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.copyItemsAux_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.copyItemsAux_complete

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.copyItems_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.copyItems_complete

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.returning_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.returning_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.returnTail_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.returnTail_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.sequencePlan_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.sequencePlan_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.pairPlan_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.pairPlan_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.continuationPlan_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.continuationPlan_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.whileBreakPlan_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.whileBreakPlan_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.whileReturnPlan_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.whileReturnPlan_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.whileContinuePlan_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.whileContinuePlan_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.forBreakPlan_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.forBreakPlan_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.forReturnPlan_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.forReturnPlan_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.forContinuePlan_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.forContinuePlan_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.doBreakPlan_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.doBreakPlan_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.doReturnPlan_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.doReturnPlan_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.doContinuePlan_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.doContinuePlan_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.blocksPlan_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.blocksPlan_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.recognize_plan_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.recognize_plan_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.recognize_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.recognize_complete

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.recognize_none_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.recognize_none_iff

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.recognize_returning_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.recognize_returning_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.recognize_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.recognize_sound

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.recognize_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.recognize_refuses

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.checkedSlot_exact' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.checkedSlot_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.primitiveSlot_exact' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.primitiveSlot_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.boolPair_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.boolPair_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.copySlots_exact' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.copySlots_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.branchSlots_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.branchSlots_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.booleanSlots_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.booleanSlots_complete

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.booleanSlots_unique' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.booleanSlots_unique

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.booleanSlots_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.booleanSlots_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.mapping_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.mapping_exact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.mapping_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.mapping_complete

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.CheckedSlot.type_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.CheckedSlot.type_eq

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.localRead_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.localRead_local

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.localCopy_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.localCopy_copy

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.copyStatement_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.copyStatement_copy

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.boolCopyStatement_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.boolCopyStatement_copy

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.boolWriteStatement_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.boolWriteStatement_set

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.operationalFact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.operationalFact

/-- info: 'Solidity.Backend.StructuredFlow.SourceDispatch.dispatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StructuredFlow.SourceDispatch.dispatch
