import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Values

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarValues
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.negatedTrue_source
theorem witness_negatedTrue_source : jointType% Solidity.Backend.Scalar.negatedTrue_source :=
  jointProof% Solidity.Backend.Scalar.negatedTrue_source [
    (default),
    ([]),
    (state0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.negatedTrue_target
theorem witness_negatedTrue_target : jointType% Solidity.Backend.Scalar.negatedTrue_target :=
  jointProof% Solidity.Backend.Scalar.negatedTrue_target [
    (default),
    ([]),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.negatedTrue_bytes
theorem witness_negatedTrue_bytes : jointType% Solidity.Backend.Scalar.negatedTrue_bytes :=
  jointProof% Solidity.Backend.Scalar.negatedTrue_bytes [
    (default),
    ([])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarValues
