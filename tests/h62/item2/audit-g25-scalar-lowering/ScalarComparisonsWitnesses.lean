import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Comparisons

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarComparisons
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.flag_not_lt
theorem witness_flag_not_lt : jointType% Solidity.Backend.Scalar.flag_not_lt :=
  jointProof% Solidity.Backend.Scalar.flag_not_lt [
    (0),
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.flag_iszero
theorem witness_flag_iszero : jointType% Solidity.Backend.Scalar.flag_iszero :=
  jointProof% Solidity.Backend.Scalar.flag_iszero [
    (false)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.encode_uint_beq
theorem witness_encode_uint_beq : jointType% Solidity.Backend.Scalar.encode_uint_beq :=
  jointProof% Solidity.Backend.Scalar.encode_uint_beq [
    (u0),
    (u0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.encode_int_beq
theorem witness_encode_int_beq : jointType% Solidity.Backend.Scalar.encode_int_beq :=
  jointProof% Solidity.Backend.Scalar.encode_int_beq [
    (i0),
    (i0)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarComparisons
