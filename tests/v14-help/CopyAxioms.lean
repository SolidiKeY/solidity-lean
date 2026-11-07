import Solidity.Backend.Aggregates.CalldataCopyControls

#print axioms Solidity.Source.mapM_lift_run
#print axioms Solidity.Source.cdToMem_array_run
#print axioms Solidity.Source.cdToMem_array_failure
#print axioms Solidity.Source.cdToMem_array_old_cell
#print axioms Solidity.Source.convRV_cdArray
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.first_word
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.second_word
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.dirty_word
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.decoded_prefix
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.copy_success
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.copied_order
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.kept_aliases
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.kept_old_objects
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.dirty_validation
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.dirty_copy_atomic
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.empty_copy_allocates
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.wrong_failure_halt
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.wrong_partial_allocation
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.actual_conversion_failure
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.copy_then_read_first
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.copy_then_read_second
#print axioms Solidity.Backend.Aggregates.CalldataCopyControls.wrong_order
#check Solidity.Source.mapM_lift_run
#check Solidity.Source.cdToMem_array_run
#check Solidity.Source.cdToMem_array_failure
#check Solidity.Source.cdToMem_array_old_cell
#check Solidity.Source.convRV_cdArray
#check Solidity.Backend.Aggregates.CalldataCopyControls.first_word
#check Solidity.Backend.Aggregates.CalldataCopyControls.second_word
#check Solidity.Backend.Aggregates.CalldataCopyControls.dirty_word
#check Solidity.Backend.Aggregates.CalldataCopyControls.decoded_prefix
#check Solidity.Backend.Aggregates.CalldataCopyControls.copy_success
#check Solidity.Backend.Aggregates.CalldataCopyControls.copied_order
#check Solidity.Backend.Aggregates.CalldataCopyControls.kept_aliases
#check Solidity.Backend.Aggregates.CalldataCopyControls.kept_old_objects
#check Solidity.Backend.Aggregates.CalldataCopyControls.dirty_validation
#check Solidity.Backend.Aggregates.CalldataCopyControls.dirty_copy_atomic
#check Solidity.Backend.Aggregates.CalldataCopyControls.empty_copy_allocates
#check Solidity.Backend.Aggregates.CalldataCopyControls.wrong_failure_halt
#check Solidity.Backend.Aggregates.CalldataCopyControls.wrong_partial_allocation
#check Solidity.Backend.Aggregates.CalldataCopyControls.actual_conversion_failure
#check Solidity.Backend.Aggregates.CalldataCopyControls.copy_then_read_first
#check Solidity.Backend.Aggregates.CalldataCopyControls.copy_then_read_second
#check Solidity.Backend.Aggregates.CalldataCopyControls.wrong_order
