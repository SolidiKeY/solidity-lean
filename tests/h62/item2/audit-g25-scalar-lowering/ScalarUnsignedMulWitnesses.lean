import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.UnsignedMul

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarUnsignedMul
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.flag_or
theorem witness_flag_or : jointType% Solidity.Backend.Scalar.flag_or :=
  jointProof% Solidity.Backend.Scalar.flag_or [
    (false),
    (false)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsignedMulTest_raw
theorem witness_unsignedMulTest_raw : jointType% Solidity.Backend.Scalar.unsignedMulTest_raw :=
  jointProof% Solidity.Backend.Scalar.unsignedMulTest_raw [
    (0),
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsignedMulTest_typed
theorem witness_unsignedMulTest_typed : jointType% Solidity.Backend.Scalar.unsignedMulTest_typed :=
  jointProof% Solidity.Backend.Scalar.unsignedMulTest_typed [
    (u0),
    (u0),
    ([99])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarUnsignedMul
