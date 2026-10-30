import Solidity.Backend.Scalar.SignedPower
import Solidity.Backend.Scalar.SignedPowerPost
import Solidity.Backend.Scalar.SignedPowerPrefix
import Solidity.Backend.Scalar.ArithmeticWidths
import Solidity.Backend.Scalar.Capacity
import Solidity.Backend.Scalar.CastChains
import Solidity.Backend.Scalar.Combinations
import Solidity.Backend.Scalar.Composition
import Solidity.Backend.Scalar.FixedBytes
import Solidity.Backend.Scalar.Select
import Solidity.Backend.Scalar.WidthGuards
import Solidity.Backend.Scalar.Bitwise
import Solidity.Backend.Scalar.Casts
import Solidity.Backend.Scalar.Checked
import Solidity.Backend.Scalar.Comparisons
import Solidity.Backend.Scalar.Division
import Solidity.Backend.Scalar.Exponentiation
import Solidity.Backend.Scalar.Guards
import Solidity.Backend.Scalar.Heights
import Solidity.Backend.Scalar.Modular
import Solidity.Backend.Scalar.Negation
import Solidity.Backend.Scalar.PowerBounds
import Solidity.Backend.Scalar.PowerGuard
import Solidity.Backend.Scalar.Shifts
import Solidity.Backend.Scalar.SignedBits
import Solidity.Backend.Scalar.SignedChecked
import Solidity.Backend.Scalar.SignedDivision
import Solidity.Backend.Scalar.SignedGuards
import Solidity.Backend.Scalar.SignedMul
import Solidity.Backend.Scalar.SignedShift
import Solidity.Backend.Scalar.Slice
import Solidity.Backend.Scalar.Typed
import Solidity.Backend.Scalar.UnsignedMul
import Solidity.Backend.Scalar.Values
import Solidity.Backend.Scalar.Widths
import Solidity.Backend.Scalar.Wrapping

/-! Regression pins for the scalar preparation lane. Keeping pins separate
from the large kernel-checked constants avoids a cold table rebuild solely
for message guards. These imports do not claim full EVM/source composition. -/
namespace Solidity.Backend.Scalar

/-- info: 'Solidity.Backend.Scalar.cast_roundtrip_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cast_roundtrip_int

/-- info: 'Solidity.Backend.Scalar.cast_roundtrip_uint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cast_roundtrip_uint

/-- info: 'Solidity.Backend.Scalar.checkedIntAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedIntAdd

/-- info: 'Solidity.Backend.Scalar.checkedIntMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedIntMul

/-- info: 'Solidity.Backend.Scalar.checkedIntSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedIntSub

/-- info: 'Solidity.Backend.Scalar.checkedUintAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintAdd

/-- info: 'Solidity.Backend.Scalar.checkedUintMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintMul

/-- info: 'Solidity.Backend.Scalar.checkedUintPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintPow

/-- info: 'Solidity.Backend.Scalar.checkedUintSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintSub

/-- info: 'Solidity.Backend.Scalar.checked_negation_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checked_negation_correct

/-- info: 'Solidity.Backend.Scalar.encodeValue_toWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms encodeValue_toWord

/-- info: 'Solidity.Backend.Scalar.guardedNext_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms guardedNext_zero

/-- info: 'Solidity.Backend.Scalar.intAnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intAnd

/-- info: 'Solidity.Backend.Scalar.intOr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intOr

/-- info: 'Solidity.Backend.Scalar.intShr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intShr

/-- info: 'Solidity.Backend.Scalar.intXor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intXor

/-- info: 'Solidity.Backend.Scalar.int_div_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms int_div_body

/-- info: 'Solidity.Backend.Scalar.int_div_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms int_div_correct

/-- info: 'Solidity.Backend.Scalar.int_div_exception' depends on axioms: [propext] -/
#guard_msgs in #print axioms int_div_exception

/-- info: 'Solidity.Backend.Scalar.int_mod_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms int_mod_body

/-- info: 'Solidity.Backend.Scalar.int_mod_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms int_mod_correct

/-- info: 'Solidity.Backend.Scalar.int_word_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms int_word_zero

/-- info: 'Solidity.Backend.Scalar.negationTest_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms negationTest_typed

/-- info: 'Solidity.Backend.Scalar.powerCell_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms powerCell_correct

/-- info: 'Solidity.Backend.Scalar.powerFits_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms powerFits_correct

/-- info: 'Solidity.Backend.Scalar.powerRows_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms powerRows_correct

/-- info: 'Solidity.Backend.Scalar.powerTest_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms powerTest_correct

/-- info: 'Solidity.Backend.Scalar.prefix_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_capacity

/-- info: 'Solidity.Backend.Scalar.run_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run_capacity

/-- info: 'Solidity.Backend.Scalar.run_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run_height

/-- info: 'Solidity.Backend.Scalar.scalarEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scalarEq

/-- info: 'Solidity.Backend.Scalar.scalarNe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scalarNe

/-- info: 'Solidity.Backend.Scalar.signedAddTest_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedAddTest_raw

/-- info: 'Solidity.Backend.Scalar.signedDivOverflowTest_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedDivOverflowTest_correct

/-- info: 'Solidity.Backend.Scalar.signedMulTest_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedMulTest_raw

/-- info: 'Solidity.Backend.Scalar.signedShiftPrefix_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedShiftPrefix_correct

/-- info: 'Solidity.Backend.Scalar.signedSubTest_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedSubTest_raw

/-- info: 'Solidity.Backend.Scalar.step_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_height

/-- info: 'Solidity.Backend.Scalar.threshold_accept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms threshold_accept

/-- info: 'Solidity.Backend.Scalar.threshold_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms threshold_bounds

/-- info: 'Solidity.Backend.Scalar.uintNot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms uintNot

/-- info: 'Solidity.Backend.Scalar.uintShl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms uintShl

/-- info: 'Solidity.Backend.Scalar.uintShr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms uintShr

/-- info: 'Solidity.Backend.Scalar.uint_div_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms uint_div_body

/-- info: 'Solidity.Backend.Scalar.uint_div_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms uint_div_correct

/-- info: 'Solidity.Backend.Scalar.uint_div_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms uint_div_zero

/-- info: 'Solidity.Backend.Scalar.uint_mod_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms uint_mod_body

/-- info: 'Solidity.Backend.Scalar.uint_mod_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms uint_mod_correct

/-- info: 'Solidity.Backend.Scalar.uint_mod_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms uint_mod_zero

/-- info: 'Solidity.Backend.Scalar.unsignedMulTest_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unsignedMulTest_raw

/-- info: 'Solidity.Backend.Scalar.wrappingPow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wrappingPow

/-- info: 'Solidity.Backend.Scalar.unsigned_addAt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unsigned_addAt_correct

/-- info: 'Solidity.Backend.Scalar.unsigned_subAt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unsigned_subAt_correct

/-- info: 'Solidity.Backend.Scalar.unsigned_mulAt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unsigned_mulAt_correct

/-- info: 'Solidity.Backend.Scalar.signed_addAt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signed_addAt_correct

/-- info: 'Solidity.Backend.Scalar.signed_subAt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signed_subAt_correct

/-- info: 'Solidity.Backend.Scalar.signed_mulAt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signed_mulAt_correct

/-- info: 'Solidity.Backend.Scalar.unsigned_divAt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unsigned_divAt_correct

/-- info: 'Solidity.Backend.Scalar.unsigned_modAt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unsigned_modAt_correct

/-- info: 'Solidity.Backend.Scalar.signed_divAt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signed_divAt_correct

/-- info: 'Solidity.Backend.Scalar.signed_modAt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signed_modAt_correct

/-- info: 'Solidity.Backend.Scalar.unsigned_powAt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unsigned_powAt_correct

/-- info: 'Solidity.Backend.Scalar.ofInt_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ofInt_low

/-- info: 'Solidity.Backend.Scalar.ClosedInvocation.prefix_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClosedInvocation.prefix_safe

/-- info: 'Solidity.Backend.Scalar.BinaryInvocation.correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BinaryInvocation.correct

/-- info: 'Solidity.Backend.Scalar.BinaryInvocation.prefix_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BinaryInvocation.prefix_safe

/-- info: 'Solidity.Backend.Scalar.CheckedInvocation.correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CheckedInvocation.correct

/-- info: 'Solidity.Backend.Scalar.CheckedInvocation.testPrefix_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CheckedInvocation.testPrefix_safe

/-- info: 'Solidity.Backend.Scalar.checkedAdditionWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedAdditionWitness

/-- info: 'Solidity.Backend.Scalar.signed_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signed_chain

/-- info: 'Solidity.Backend.Scalar.unsigned_after_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unsigned_after_signed

/-- info: 'Solidity.Backend.Scalar.signedAt_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedAt_word

/-- info: 'Solidity.Backend.Scalar.signedExpansion_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedExpansion_correct

/-- info: 'Solidity.Backend.Scalar.mixedWidthCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mixedWidthCertificate

/-- info: 'Solidity.Backend.Scalar.mixedWidthInvocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mixedWidthInvocation

/-- info: 'Solidity.Backend.Scalar.mixedWidth_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mixedWidth_source

/-- info: 'Solidity.Backend.Scalar.mixedWidth_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mixedWidth_target

/-- info: 'Solidity.Backend.Scalar.BinaryCertificate.unsignedWidth_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms BinaryCertificate.unsignedWidth_correct

/-- info: 'Solidity.Backend.Scalar.BinaryCertificate.signedWidth_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms BinaryCertificate.signedWidth_correct

/-- info: 'Solidity.Backend.Scalar.UnaryCertificate.unsignedWidth_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms UnaryCertificate.unsignedWidth_correct

/-- info: 'Solidity.Backend.Scalar.UnaryCertificate.signedWidth_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms UnaryCertificate.signedWidth_correct

/-- info: 'Solidity.Backend.Scalar.bytesWiden_intrinsic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bytesWiden_intrinsic

/-- info: 'Solidity.Backend.Scalar.bytesNarrow_intrinsic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bytesNarrow_intrinsic

/-- info: 'Solidity.Backend.Scalar.bytesResize_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bytesResize_correct

/-- info: 'Solidity.Backend.Scalar.bytesResize_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bytesResize_range

/-- info: 'Solidity.Backend.Scalar.selectModular' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms selectModular

/-- info: 'Solidity.Backend.Scalar.selectUnary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms selectUnary

/-- info: 'Solidity.Backend.Scalar.selectBinary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms selectBinary

/-- info: 'Solidity.Backend.Scalar.selectChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms selectChecked

/-- info: 'Solidity.Backend.Scalar.selectCheckedUnary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms selectCheckedUnary

/-- info: 'Solidity.Backend.Scalar.binary_selection_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms binary_selection_coverage

/-- info: 'Solidity.Backend.Scalar.unary_selection_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unary_selection_coverage

/-- info: 'Solidity.Backend.Scalar.checkedIntNeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedIntNeg

/-- info: 'Solidity.Backend.Scalar.unsignedWidth_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unsignedWidth_guarded

/-- info: 'Solidity.Backend.Scalar.signedWidth_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedWidth_guarded

/-- info: 'Solidity.Backend.Scalar.unsignedWidthTest_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unsignedWidthTest_correct

/-- info: 'Solidity.Backend.Scalar.signedWidthTest_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedWidthTest_correct

/-- info: 'Solidity.Backend.Scalar.bytesResize_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bytesResize_roundtrip

/-- info: 'Solidity.Backend.Scalar.signedPower_negative_three_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedPower_negative_three_source

/-- info: 'Solidity.Backend.Scalar.signedPower_minimum_one_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedPower_minimum_one_source

/-- info: 'Solidity.Backend.Scalar.signedPower_positive_boundary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms signedPower_positive_boundary_source

/-- info: 'Solidity.Backend.Scalar.signedPower_unsigned_overflow_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms signedPower_unsigned_overflow_source

/-- info: 'Solidity.Backend.Scalar.signedPower_negative_three_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedPower_negative_three_target

/-- info: 'Solidity.Backend.Scalar.signedPower_minimum_one_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedPower_minimum_one_target

/-- info: 'Solidity.Backend.Scalar.signedPower_positive_boundary_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms signedPower_positive_boundary_target

/-- info: 'Solidity.Backend.Scalar.signedPower_unsigned_overflow_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms signedPower_unsigned_overflow_target

/-- info: 'Solidity.Backend.Scalar.signedPowerWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedPowerWitness

/-- info: 'Solidity.Backend.Scalar.SignedPowerInvocation.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SignedPowerInvocation.correct

/-- info: 'Solidity.Backend.Scalar.signedPower_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedPower_correct

/-- info: 'Solidity.Backend.Scalar.powerSourceResult_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms powerSourceResult_map

/-- info: 'Solidity.Backend.Scalar.signedPower_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signedPower_source

/-- info: 'Solidity.Backend.Scalar.powerPostTest_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms powerPostTest_correct

/-- info: 'Solidity.Backend.Scalar.powerSignBody_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms powerSignBody_correct

/-- info: 'Solidity.Backend.Scalar.powerPost_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms powerPost_correct

/-- info: 'Solidity.Backend.Scalar.powerPost_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms powerPost_source

/-- info: 'Solidity.Backend.Scalar.parity_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms parity_word

/-- info: 'Solidity.Backend.Scalar.powerNegativePrefix_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms powerNegativePrefix_correct

/-- info: 'Solidity.Backend.Scalar.powerAbsPrefix_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms powerAbsPrefix_correct

/-- info: 'Solidity.Backend.Scalar.powerPrepare_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms powerPrepare_correct

end Solidity.Backend.Scalar
