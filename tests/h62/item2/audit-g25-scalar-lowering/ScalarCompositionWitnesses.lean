import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Composition

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarComposition
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.BinaryCertificate.unsignedWidth_correct
theorem witness_BinaryCertificate_unsignedWidth_correct : jointType% Solidity.Backend.Scalar.BinaryCertificate.unsignedWidth_correct :=
  jointProof% Solidity.Backend.Scalar.BinaryCertificate.unsignedWidth_correct [
    (.and),
    (.bool),
    (by first | rfl | decide +kernel),
    (booleanAnd),
    (⟨0, by decide⟩),
    (true),
    (true),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.BinaryCertificate.signedWidth_correct
theorem witness_BinaryCertificate_signedWidth_correct : jointType% Solidity.Backend.Scalar.BinaryCertificate.signedWidth_correct :=
  jointProof% Solidity.Backend.Scalar.BinaryCertificate.signedWidth_correct [
    (.and),
    (.bool),
    (by first | rfl | decide +kernel),
    (booleanAnd),
    (⟨0, by decide⟩),
    (true),
    (true),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.UnaryCertificate.unsignedWidth_correct
theorem witness_UnaryCertificate_unsignedWidth_correct : jointType% Solidity.Backend.Scalar.UnaryCertificate.unsignedWidth_correct :=
  jointProof% Solidity.Backend.Scalar.UnaryCertificate.unsignedWidth_correct [
    (.not),
    (.bool),
    (by first | rfl | decide +kernel),
    (booleanNot),
    (⟨0, by decide⟩),
    (true),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.UnaryCertificate.signedWidth_correct
theorem witness_UnaryCertificate_signedWidth_correct : jointType% Solidity.Backend.Scalar.UnaryCertificate.signedWidth_correct :=
  jointProof% Solidity.Backend.Scalar.UnaryCertificate.signedWidth_correct [
    (.not),
    (.bool),
    (by first | rfl | decide +kernel),
    (booleanNot),
    (⟨0, by decide⟩),
    (true),
    ([99])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarComposition
