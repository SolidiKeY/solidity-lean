import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Typed

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarTyped
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.uint_range
theorem witness_uint_range : jointType% Solidity.Backend.Scalar.uint_range :=
  jointProof% Solidity.Backend.Scalar.uint_range [
    (u0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.int_range
theorem witness_int_range : jointType% Solidity.Backend.Scalar.int_range :=
  jointProof% Solidity.Backend.Scalar.int_range [
    (i0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.encode_uint_toNat
theorem witness_encode_uint_toNat : jointType% Solidity.Backend.Scalar.encode_uint_toNat :=
  jointProof% Solidity.Backend.Scalar.encode_uint_toNat [
    (u0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.encode_int_toInt
theorem witness_encode_int_toInt : jointType% Solidity.Backend.Scalar.encode_int_toInt :=
  jointProof% Solidity.Backend.Scalar.encode_int_toInt [
    (i0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.encode_int_injective
theorem witness_encode_int_injective : jointType% Solidity.Backend.Scalar.encode_int_injective :=
  jointProof% Solidity.Backend.Scalar.encode_int_injective [
    (i0),
    (i0),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.encode_uint_injective
theorem witness_encode_uint_injective : jointType% Solidity.Backend.Scalar.encode_uint_injective :=
  jointProof% Solidity.Backend.Scalar.encode_uint_injective [
    (u0),
    (u0),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.encodeValue_toWord
theorem witness_encodeValue_toWord : jointType% Solidity.Backend.Scalar.encodeValue_toWord :=
  jointProof% Solidity.Backend.Scalar.encodeValue_toWord [
    (.bool),
    (true)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.literal_correct
theorem witness_literal_correct : jointType% Solidity.Backend.Scalar.literal_correct :=
  jointProof% Solidity.Backend.Scalar.literal_correct [
    (.bool),
    (true),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.booleanNe_bytes
theorem witness_booleanNe_bytes : jointType% Solidity.Backend.Scalar.booleanNe_bytes :=
  jointProof% Solidity.Backend.Scalar.booleanNe_bytes []

-- AUDIT-WITNESS: Solidity.Backend.Scalar.booleanNot_bytes
theorem witness_booleanNot_bytes : jointType% Solidity.Backend.Scalar.booleanNot_bytes :=
  jointProof% Solidity.Backend.Scalar.booleanNot_bytes []

end Solidity.Backend.Scalar.H62Audit.ScalarTyped
