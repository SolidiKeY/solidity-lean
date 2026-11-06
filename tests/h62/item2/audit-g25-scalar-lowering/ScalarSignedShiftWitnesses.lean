import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.SignedShift

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarSignedShift
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedShiftPrefix_correct
theorem witness_signedShiftPrefix_correct : jointType% Solidity.Backend.Scalar.signedShiftPrefix_correct :=
  jointProof% Solidity.Backend.Scalar.signedShiftPrefix_correct [
    (0),
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedShift_raw
theorem witness_signedShift_raw : jointType% Solidity.Backend.Scalar.signedShift_raw :=
  jointProof% Solidity.Backend.Scalar.signedShift_raw [
    (0),
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.sar_zero
theorem witness_sar_zero : jointType% Solidity.Backend.Scalar.sar_zero :=
  jointProof% Solidity.Backend.Scalar.sar_zero [
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.encode_int_toNat_of_nonneg
theorem witness_encode_int_toNat_of_nonneg : jointType% Solidity.Backend.Scalar.encode_int_toNat_of_nonneg :=
  jointProof% Solidity.Backend.Scalar.encode_int_toNat_of_nonneg [
    (i0),
    (by first | rfl | decide +kernel)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarSignedShift
