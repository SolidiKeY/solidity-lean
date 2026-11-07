import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.SignedMul

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarSignedMul
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.toWord_ofInt
theorem witness_toWord_ofInt : jointType% Solidity.Backend.Scalar.toWord_ofInt :=
  jointProof% Solidity.Backend.Scalar.toWord_ofInt [
    (0),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedMulTest_raw
theorem witness_signedMulTest_raw : jointType% Solidity.Backend.Scalar.signedMulTest_raw :=
  jointProof% Solidity.Backend.Scalar.signedMulTest_raw [
    (0),
    (0),
    ([99])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarSignedMul
