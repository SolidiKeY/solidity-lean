import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Shifts

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarShifts
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.shiftLeft_word
theorem witness_shiftLeft_word : jointType% Solidity.Backend.Scalar.shiftLeft_word :=
  jointProof% Solidity.Backend.Scalar.shiftLeft_word [
    (0),
    (0)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarShifts
