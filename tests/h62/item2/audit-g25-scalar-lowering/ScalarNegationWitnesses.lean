import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Negation

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarNegation
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.negationTest_typed
theorem witness_negationTest_typed : jointType% Solidity.Backend.Scalar.negationTest_typed :=
  jointProof% Solidity.Backend.Scalar.negationTest_typed [
    (i0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.negationBody_typed
theorem witness_negationBody_typed : jointType% Solidity.Backend.Scalar.negationBody_typed :=
  jointProof% Solidity.Backend.Scalar.negationBody_typed [
    (i0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.checked_negation_correct
theorem witness_checked_negation_correct : jointType% Solidity.Backend.Scalar.checked_negation_correct :=
  jointProof% Solidity.Backend.Scalar.checked_negation_correct [
    (i0),
    ([99])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarNegation
