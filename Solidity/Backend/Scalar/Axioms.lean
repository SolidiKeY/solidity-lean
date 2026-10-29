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

end Solidity.Backend.Scalar
