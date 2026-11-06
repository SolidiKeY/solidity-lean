import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Guards

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarGuards
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.zeroTest_correct
theorem witness_zeroTest_correct : jointType% Solidity.Backend.Scalar.zeroTest_correct :=
  jointProof% Solidity.Backend.Scalar.zeroTest_correct [
    (⟨0, by decide⟩),
    ([0,99]),
    (0),
    (rfl)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.guarded_zero
theorem witness_guarded_zero : jointType% Solidity.Backend.Scalar.guarded_zero :=
  jointProof% Solidity.Backend.Scalar.guarded_zero [
    (⟨0, by decide⟩),
    ([0,99]),
    (0),
    ([]),
    ([]),
    (rfl)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarGuards
