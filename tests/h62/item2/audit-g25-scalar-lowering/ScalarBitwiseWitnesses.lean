import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Bitwise

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarBitwise
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.encoded_word
theorem witness_encoded_word : jointType% Solidity.Backend.Scalar.encoded_word :=
  jointProof% Solidity.Backend.Scalar.encoded_word [
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.uintBitwise_encoded
theorem witness_uintBitwise_encoded : jointType% Solidity.Backend.Scalar.uintBitwise_encoded :=
  jointProof% Solidity.Backend.Scalar.uintBitwise_encoded [
    (fun _ _ => 0),
    (u0),
    (u0),
    (0),
    (rfl),
    ([99])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarBitwise
