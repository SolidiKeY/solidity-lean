import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Checked

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarChecked
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.guarded_range_correct
theorem witness_guarded_range_correct : jointType% Solidity.Backend.Scalar.guarded_range_correct :=
  jointProof% Solidity.Backend.Scalar.guarded_range_correct [
    ([pushWord 0]),
    ([.op .ADD]),
    (u0),
    (u0),
    (0),
    ([99]),
    (by decide +kernel),
    (by decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsignedAddTest_raw
theorem witness_unsignedAddTest_raw : jointType% Solidity.Backend.Scalar.unsignedAddTest_raw :=
  jointProof% Solidity.Backend.Scalar.unsignedAddTest_raw [
    (0),
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsignedSubTest_raw
theorem witness_unsignedSubTest_raw : jointType% Solidity.Backend.Scalar.unsignedSubTest_raw :=
  jointProof% Solidity.Backend.Scalar.unsignedSubTest_raw [
    (0),
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsignedAddTest_typed
theorem witness_unsignedAddTest_typed : jointType% Solidity.Backend.Scalar.unsignedAddTest_typed :=
  jointProof% Solidity.Backend.Scalar.unsignedAddTest_typed [
    (u0),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsignedSubTest_typed
theorem witness_unsignedSubTest_typed : jointType% Solidity.Backend.Scalar.unsignedSubTest_typed :=
  jointProof% Solidity.Backend.Scalar.unsignedSubTest_typed [
    (u0),
    (u0),
    ([99])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarChecked
