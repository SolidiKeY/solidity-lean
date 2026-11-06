import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.WidthGuards

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarWidthGuards
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsignedWidthTest_correct
theorem witness_unsignedWidthTest_correct : jointType% Solidity.Backend.Scalar.unsignedWidthTest_correct :=
  jointProof% Solidity.Backend.Scalar.unsignedWidthTest_correct [
    (⟨0, by decide⟩),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedWidthTest_correct
theorem witness_signedWidthTest_correct : jointType% Solidity.Backend.Scalar.signedWidthTest_correct :=
  jointProof% Solidity.Backend.Scalar.signedWidthTest_correct [
    (⟨0, by decide⟩),
    (i0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsignedWidth_guarded
theorem witness_unsignedWidth_guarded : jointType% Solidity.Backend.Scalar.unsignedWidth_guarded :=
  jointProof% Solidity.Backend.Scalar.unsignedWidth_guarded [
    (⟨0, by decide⟩),
    (u0),
    ([99]),
    ([1,2])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedWidth_guarded
theorem witness_signedWidth_guarded : jointType% Solidity.Backend.Scalar.signedWidth_guarded :=
  jointProof% Solidity.Backend.Scalar.signedWidth_guarded [
    (⟨0, by decide⟩),
    (i0),
    ([99]),
    ([1,2])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarWidthGuards
