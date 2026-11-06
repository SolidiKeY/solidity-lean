import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Division

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarDivision
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.uint_div_body
theorem witness_uint_div_body : jointType% Solidity.Backend.Scalar.uint_div_body :=
  jointProof% Solidity.Backend.Scalar.uint_div_body [
    (u0),
    (u1),
    (by decide +kernel),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.uint_mod_body
theorem witness_uint_mod_body : jointType% Solidity.Backend.Scalar.uint_mod_body :=
  jointProof% Solidity.Backend.Scalar.uint_mod_body [
    (u0),
    (u1),
    (by decide +kernel),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.uint_div_zero
theorem witness_uint_div_zero : jointType% Solidity.Backend.Scalar.uint_div_zero :=
  jointProof% Solidity.Backend.Scalar.uint_div_zero [
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.uint_mod_zero
theorem witness_uint_mod_zero : jointType% Solidity.Backend.Scalar.uint_mod_zero :=
  jointProof% Solidity.Backend.Scalar.uint_mod_zero [
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.uint_div_correct
theorem witness_uint_div_correct : jointType% Solidity.Backend.Scalar.uint_div_correct :=
  jointProof% Solidity.Backend.Scalar.uint_div_correct [
    (u0),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.uint_mod_correct
theorem witness_uint_mod_correct : jointType% Solidity.Backend.Scalar.uint_mod_correct :=
  jointProof% Solidity.Backend.Scalar.uint_mod_correct [
    (u0),
    (u0),
    ([99])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarDivision
