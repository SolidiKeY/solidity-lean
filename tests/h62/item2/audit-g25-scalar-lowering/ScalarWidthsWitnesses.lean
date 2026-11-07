import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Widths

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarWidths
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.widthBits_bounds
theorem witness_widthBits_bounds : jointType% Solidity.Backend.Scalar.widthBits_bounds :=
  jointProof% Solidity.Backend.Scalar.widthBits_bounds [
    (⟨0, by decide⟩)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsigned_correct
theorem witness_unsigned_correct : jointType% Solidity.Backend.Scalar.unsigned_correct :=
  jointProof% Solidity.Backend.Scalar.unsigned_correct [
    (⟨0, by decide⟩),
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signed_correct
theorem witness_signed_correct : jointType% Solidity.Backend.Scalar.signed_correct :=
  jointProof% Solidity.Backend.Scalar.signed_correct [
    (⟨0, by decide⟩),
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsigned_chain
theorem witness_unsigned_chain : jointType% Solidity.Backend.Scalar.unsigned_chain :=
  jointProof% Solidity.Backend.Scalar.unsigned_chain [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (by first | rfl | decide +kernel),
    (0)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarWidths
