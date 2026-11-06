import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.SignedGuards

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarSignedGuards
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedDivOverflowTest_correct
theorem witness_signedDivOverflowTest_correct : jointType% Solidity.Backend.Scalar.signedDivOverflowTest_correct :=
  jointProof% Solidity.Backend.Scalar.signedDivOverflowTest_correct [
    (i0),
    (i0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.guardedNext_zero
theorem witness_guardedNext_zero : jointType% Solidity.Backend.Scalar.guardedNext_zero :=
  jointProof% Solidity.Backend.Scalar.guardedNext_zero [
    (⟨0, by decide⟩),
    ([0,99]),
    (0),
    ([]),
    (fun st => some (.ok st)),
    (rfl)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.int_div_correct
theorem witness_int_div_correct : jointType% Solidity.Backend.Scalar.int_div_correct :=
  jointProof% Solidity.Backend.Scalar.int_div_correct [
    (i0),
    (i0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.int_mod_correct
theorem witness_int_mod_correct : jointType% Solidity.Backend.Scalar.int_mod_correct :=
  jointProof% Solidity.Backend.Scalar.int_mod_correct [
    (i0),
    (i0),
    ([99])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarSignedGuards
