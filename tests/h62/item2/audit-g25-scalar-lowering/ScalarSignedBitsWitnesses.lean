import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.SignedBits

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarSignedBits
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedOf_word
theorem witness_signedOf_word : jointType% Solidity.Backend.Scalar.signedOf_word :=
  jointProof% Solidity.Backend.Scalar.signedOf_word [
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.wordOf_int
theorem witness_wordOf_int : jointType% Solidity.Backend.Scalar.wordOf_int :=
  jointProof% Solidity.Backend.Scalar.wordOf_int [
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.encoded_signed_word
theorem witness_encoded_signed_word : jointType% Solidity.Backend.Scalar.encoded_signed_word :=
  jointProof% Solidity.Backend.Scalar.encoded_signed_word [
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedBitwise_read
theorem witness_signedBitwise_read : jointType% Solidity.Backend.Scalar.signedBitwise_read :=
  jointProof% Solidity.Backend.Scalar.signedBitwise_read [
    (fun _ _ => 0),
    (by intro _ _ _ _; exact (by decide : (0 : Nat) < 2^255)),
    (0),
    (0),
    (by decide +kernel),
    (by decide +kernel),
    (0),
    (rfl)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarSignedBits
