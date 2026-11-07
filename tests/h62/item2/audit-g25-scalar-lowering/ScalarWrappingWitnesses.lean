import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Wrapping

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarWrapping
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.encoded_mod
theorem witness_encoded_mod : jointType% Solidity.Backend.Scalar.encoded_mod :=
  jointProof% Solidity.Backend.Scalar.encoded_mod [
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.wrappingAdd_narrow
theorem witness_wrappingAdd_narrow : jointType% Solidity.Backend.Scalar.wrappingAdd_narrow :=
  jointProof% Solidity.Backend.Scalar.wrappingAdd_narrow [
    (⟨0, by decide⟩),
    (0),
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.wrappingAdd_signed
theorem witness_wrappingAdd_signed : jointType% Solidity.Backend.Scalar.wrappingAdd_signed :=
  jointProof% Solidity.Backend.Scalar.wrappingAdd_signed [
    (⟨0, by decide⟩),
    (0),
    (0),
    ([99])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarWrapping
