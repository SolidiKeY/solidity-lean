import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Select

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarSelect
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.binary_selection_coverage
theorem witness_binary_selection_coverage : jointType% Solidity.Backend.Scalar.binary_selection_coverage :=
  jointProof% Solidity.Backend.Scalar.binary_selection_coverage [
    (.and),
    (.bool),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unary_selection_coverage
theorem witness_unary_selection_coverage : jointType% Solidity.Backend.Scalar.unary_selection_coverage :=
  jointProof% Solidity.Backend.Scalar.unary_selection_coverage [
    (.not),
    (.bool),
    (by first | rfl | decide +kernel)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarSelect
