import Solidity.Lowering.V07.UnsignedAddition
import Solidity.Lowering.V07.UnsignedMultiplication
import Solidity.Lowering.V07.WordCasts
import Solidity.Lowering.V07.ConditionalAssignments
import Solidity.Lowering.V07.WrappedMultiplicationPair
import Solidity.Lowering.V07.SignedWordSubtraction
import Solidity.Lowering.V07.ReferenceCaptureRelated
import Solidity.Lowering.V07.ReferenceOrderRelated
import Solidity.Lowering.V07.LocationGraphCompleteness

/-! Exact axiom guards for selected V07 arithmetic, cast, effect, reference and
structural graph headlines. Registered in the default import closure. These
guards add no admission, missing producer, production or coverage theorem. -/

/-- info: 'Solidity.Lowering.V07.UnsignedAddition.source_add_unchecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedAddition.source_add_unchecked

/-- info: 'Solidity.Lowering.V07.UnsignedAddition.word_add_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedAddition.word_add_eval

/-- info: 'Solidity.Lowering.V07.UnsignedAddition.add_value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedAddition.add_value_run

/-- info: 'Solidity.Lowering.V07.UnsignedAddition.source_from_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedAddition.source_from_pair

/-- info: 'Solidity.Lowering.V07.UnsignedAddition.source_locals_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedAddition.source_locals_run

/-- info: 'Solidity.Lowering.V07.UnsignedAddition.locals_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedAddition.locals_transport

/-- info: 'Solidity.Lowering.V07.UnsignedAddition.source_assign_read_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedAddition.source_assign_read_run

/-- info: 'Solidity.Lowering.V07.UnsignedAddition.assign_read_operand_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedAddition.assign_read_operand_run

/-- info: 'Solidity.Lowering.V07.UnsignedAddition.assignment_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedAddition.assignment_transport

/-- info: 'Solidity.Lowering.V07.UnsignedAddition.assignment_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedAddition.assignment_extension

/-- info: 'Solidity.Lowering.V07.UnsignedMultiplication.source_mul_unchecked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedMultiplication.source_mul_unchecked

/-- info: 'Solidity.Lowering.V07.UnsignedMultiplication.word_mul_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedMultiplication.word_mul_eval

/-- info: 'Solidity.Lowering.V07.UnsignedMultiplication.mul_value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedMultiplication.mul_value_run

/-- info: 'Solidity.Lowering.V07.UnsignedMultiplication.source_from_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedMultiplication.source_from_pair

/-- info: 'Solidity.Lowering.V07.UnsignedMultiplication.source_locals_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedMultiplication.source_locals_run

/-- info: 'Solidity.Lowering.V07.UnsignedMultiplication.locals_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedMultiplication.locals_transport

/-- info: 'Solidity.Lowering.V07.UnsignedMultiplication.source_assign_read_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedMultiplication.source_assign_read_run

/-- info: 'Solidity.Lowering.V07.UnsignedMultiplication.assign_read_operand_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedMultiplication.assign_read_operand_run

/-- info: 'Solidity.Lowering.V07.UnsignedMultiplication.assignment_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedMultiplication.assignment_transport

/-- info: 'Solidity.Lowering.V07.UnsignedMultiplication.assignment_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedMultiplication.assignment_extension

/-- info: 'Solidity.Lowering.V07.WordCasts.signed_wrap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WordCasts.signed_wrap

/-- info: 'Solidity.Lowering.V07.WordCasts.to_int_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WordCasts.to_int_eval

/-- info: 'Solidity.Lowering.V07.WordCasts.to_uint_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WordCasts.to_uint_eval

/-- info: 'Solidity.Lowering.V07.WordCasts.to_int_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WordCasts.to_int_run

/-- info: 'Solidity.Lowering.V07.WordCasts.to_uint_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WordCasts.to_uint_run

/-- info: 'Solidity.Lowering.V07.WordCasts.source_to_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WordCasts.source_to_int

/-- info: 'Solidity.Lowering.V07.WordCasts.source_to_uint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WordCasts.source_to_uint

/-- info: 'Solidity.Lowering.V07.WordCasts.assigned_to_int_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WordCasts.assigned_to_int_run

/-- info: 'Solidity.Lowering.V07.WordCasts.assigned_to_uint_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WordCasts.assigned_to_uint_run

/-- info: 'Solidity.Lowering.V07.WordCasts.assignment_to_int_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WordCasts.assignment_to_int_transport

/-- info: 'Solidity.Lowering.V07.WordCasts.assigned_to_int_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WordCasts.assigned_to_int_extension

/-- info: 'Solidity.Lowering.V07.WordCasts.assignment_to_uint_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WordCasts.assignment_to_uint_transport

/-- info: 'Solidity.Lowering.V07.WordCasts.assigned_to_uint_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WordCasts.assigned_to_uint_extension

/-- info: 'Solidity.Lowering.V07.ConditionalAssignments.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.ConditionalAssignments.source_run

/-- info: 'Solidity.Lowering.V07.ConditionalAssignments.branch_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.ConditionalAssignments.branch_run

/-- info: 'Solidity.Lowering.V07.ConditionalAssignments.prefix_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.ConditionalAssignments.prefix_run

/-- info: 'Solidity.Lowering.V07.ConditionalAssignments.operand_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.ConditionalAssignments.operand_run

/-- info: 'Solidity.Lowering.V07.ConditionalAssignments.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.ConditionalAssignments.transport

/-- info: 'Solidity.Lowering.V07.ConditionalAssignments.extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.ConditionalAssignments.extension

/-- info: 'Solidity.Lowering.V07.ConditionalAssignments.untouched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.ConditionalAssignments.untouched

/-- info: 'Solidity.Lowering.V07.WrappedMultiplicationPair.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WrappedMultiplicationPair.source_run

/-- info: 'Solidity.Lowering.V07.WrappedMultiplicationPair.operand_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WrappedMultiplicationPair.operand_run

/-- info: 'Solidity.Lowering.V07.WrappedMultiplicationPair.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WrappedMultiplicationPair.transport

/-- info: 'Solidity.Lowering.V07.WrappedMultiplicationPair.extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.WrappedMultiplicationPair.extension

/-- info: 'Solidity.Lowering.V07.SignedWordSubtraction.wrap_of_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedWordSubtraction.wrap_of_range

/-- info: 'Solidity.Lowering.V07.SignedWordSubtraction.wrap_word' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedWordSubtraction.wrap_word

/-- info: 'Solidity.Lowering.V07.SignedWordSubtraction.unsigned_sub_wrap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedWordSubtraction.unsigned_sub_wrap

/-- info: 'Solidity.Lowering.V07.SignedWordSubtraction.source_sub_unchecked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedWordSubtraction.source_sub_unchecked

/-- info: 'Solidity.Lowering.V07.SignedWordSubtraction.sub_value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedWordSubtraction.sub_value_run

/-- info: 'Solidity.Lowering.V07.SignedWordSubtraction.source_from_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedWordSubtraction.source_from_pair

/-- info: 'Solidity.Lowering.V07.SignedWordSubtraction.source_locals_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedWordSubtraction.source_locals_run

/-- info: 'Solidity.Lowering.V07.SignedWordSubtraction.locals_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedWordSubtraction.locals_transport

/-- info: 'Solidity.Lowering.V07.SignedWordSubtraction.source_assign_read_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedWordSubtraction.source_assign_read_run

/-- info: 'Solidity.Lowering.V07.SignedWordSubtraction.assign_read_operand_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedWordSubtraction.assign_read_operand_run

/-- info: 'Solidity.Lowering.V07.SignedWordSubtraction.assignment_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedWordSubtraction.assignment_transport

/-- info: 'Solidity.Lowering.V07.SignedWordSubtraction.assignment_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedWordSubtraction.assignment_extension

/-- info: 'Solidity.Lowering.V07.related_memory_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.related_memory_capture

/-- info: 'Solidity.Lowering.V07.related_storage_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.related_storage_capture

/-- info: 'Solidity.Lowering.V07.related_reference_assignment_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.related_reference_assignment_pair

/-- info: 'Solidity.Lowering.V07.LocationGraphCompleteness.fields_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LocationGraphCompleteness.fields_exact

/-- info: 'Solidity.Lowering.V07.LocationGraphCompleteness.producer_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LocationGraphCompleteness.producer_success
