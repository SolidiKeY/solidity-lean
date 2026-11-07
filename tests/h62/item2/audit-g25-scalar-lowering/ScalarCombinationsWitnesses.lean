import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Combinations

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarCombinations
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.mixedWidth_source
theorem witness_mixedWidth_source : jointType% Solidity.Backend.Scalar.mixedWidth_source :=
  jointProof% Solidity.Backend.Scalar.mixedWidth_source [
    (default),
    ([]),
    (state0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.mixedWidth_target
theorem witness_mixedWidth_target : jointType% Solidity.Backend.Scalar.mixedWidth_target :=
  jointProof% Solidity.Backend.Scalar.mixedWidth_target [
    (default),
    ([]),
    ([99])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarCombinations
