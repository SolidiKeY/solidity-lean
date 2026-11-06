import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.CastChains

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarCastChains
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.width_half
theorem witness_width_half : jointType% Solidity.Backend.Scalar.width_half :=
  jointProof% Solidity.Backend.Scalar.width_half [
    (⟨0, by decide⟩)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsignedClean_nat
theorem witness_unsignedClean_nat : jointType% Solidity.Backend.Scalar.unsignedClean_nat :=
  jointProof% Solidity.Backend.Scalar.unsignedClean_nat [
    (⟨0, by decide⟩),
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.shifted_low
theorem witness_shifted_low : jointType% Solidity.Backend.Scalar.shifted_low :=
  jointProof% Solidity.Backend.Scalar.shifted_low [
    (⟨0, by decide⟩),
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedAt_word
theorem witness_signedAt_word : jointType% Solidity.Backend.Scalar.signedAt_word :=
  jointProof% Solidity.Backend.Scalar.signedAt_word [
    (⟨0, by decide⟩),
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedExpansion_correct
theorem witness_signedExpansion_correct : jointType% Solidity.Backend.Scalar.signedExpansion_correct :=
  jointProof% Solidity.Backend.Scalar.signedExpansion_correct [
    (⟨0, by decide⟩),
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedClean_nat
theorem witness_signedClean_nat : jointType% Solidity.Backend.Scalar.signedClean_nat :=
  jointProof% Solidity.Backend.Scalar.signedClean_nat [
    (⟨0, by decide⟩),
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signed_low_chain
theorem witness_signed_low_chain : jointType% Solidity.Backend.Scalar.signed_low_chain :=
  jointProof% Solidity.Backend.Scalar.signed_low_chain [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (by first | rfl | decide +kernel),
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signed_chain
theorem witness_signed_chain : jointType% Solidity.Backend.Scalar.signed_chain :=
  jointProof% Solidity.Backend.Scalar.signed_chain [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (by first | rfl | decide +kernel),
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsigned_after_signed
theorem witness_unsigned_after_signed : jointType% Solidity.Backend.Scalar.unsigned_after_signed :=
  jointProof% Solidity.Backend.Scalar.unsigned_after_signed [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (by first | rfl | decide +kernel),
    (0)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarCastChains
