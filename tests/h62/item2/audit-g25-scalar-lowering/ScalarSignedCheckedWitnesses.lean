import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.SignedChecked

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarSignedChecked
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.flag_xor
theorem witness_flag_xor : jointType% Solidity.Backend.Scalar.flag_xor :=
  jointProof% Solidity.Backend.Scalar.flag_xor [
    (false),
    (false)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.xor_range
theorem witness_xor_range : jointType% Solidity.Backend.Scalar.xor_range :=
  jointProof% Solidity.Backend.Scalar.xor_range [
    (True),
    (True),
    (True),
    (inferInstance),
    (inferInstance),
    (inferInstance),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.sgn_word
theorem witness_sgn_word : jointType% Solidity.Backend.Scalar.sgn_word :=
  jointProof% Solidity.Backend.Scalar.sgn_word [
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedAddTest_raw
theorem witness_signedAddTest_raw : jointType% Solidity.Backend.Scalar.signedAddTest_raw :=
  jointProof% Solidity.Backend.Scalar.signedAddTest_raw [
    (0),
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedSubTest_raw
theorem witness_signedSubTest_raw : jointType% Solidity.Backend.Scalar.signedSubTest_raw :=
  jointProof% Solidity.Backend.Scalar.signedSubTest_raw [
    (0),
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.guarded_int_range_correct
theorem witness_guarded_int_range_correct : jointType% Solidity.Backend.Scalar.guarded_int_range_correct :=
  jointProof% Solidity.Backend.Scalar.guarded_int_range_correct [
    ([pushWord 0]),
    ([.op .ADD]),
    (i0),
    (i0),
    (0),
    ([99]),
    (by decide +kernel),
    (by decide +kernel)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarSignedChecked
