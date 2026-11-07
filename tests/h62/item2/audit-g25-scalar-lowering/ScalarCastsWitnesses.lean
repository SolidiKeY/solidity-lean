import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Casts

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarCasts
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.encoded_int
theorem witness_encoded_int : jointType% Solidity.Backend.Scalar.encoded_int :=
  jointProof% Solidity.Backend.Scalar.encoded_int [
    (0),
    (by first | rfl | decide +kernel),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.encoded_uint
theorem witness_encoded_uint : jointType% Solidity.Backend.Scalar.encoded_uint :=
  jointProof% Solidity.Backend.Scalar.encoded_uint [
    (0),
    (by first | rfl | decide +kernel),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.ofInt_sub_word
theorem witness_ofInt_sub_word : jointType% Solidity.Backend.Scalar.ofInt_sub_word :=
  jointProof% Solidity.Backend.Scalar.ofInt_sub_word [
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.cast_code_chain
theorem witness_cast_code_chain : jointType% Solidity.Backend.Scalar.cast_code_chain :=
  jointProof% Solidity.Backend.Scalar.cast_code_chain [
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.cast_roundtrip_uint
theorem witness_cast_roundtrip_uint : jointType% Solidity.Backend.Scalar.cast_roundtrip_uint :=
  jointProof% Solidity.Backend.Scalar.cast_roundtrip_uint [
    (u0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.cast_roundtrip_int
theorem witness_cast_roundtrip_int : jointType% Solidity.Backend.Scalar.cast_roundtrip_int :=
  jointProof% Solidity.Backend.Scalar.cast_roundtrip_int [
    (i0)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarCasts
