import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.SignedDivision

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarSignedDivision
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.int_word_zero
theorem witness_int_word_zero : jointType% Solidity.Backend.Scalar.int_word_zero :=
  jointProof% Solidity.Backend.Scalar.int_word_zero [
    (i0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.int_div_body
theorem witness_int_div_body : jointType% Solidity.Backend.Scalar.int_div_body :=
  jointProof% Solidity.Backend.Scalar.int_div_body [
    (i0),
    (i1),
    (by decide +kernel),
    (by decide +kernel),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.int_mod_body
theorem witness_int_mod_body : jointType% Solidity.Backend.Scalar.int_mod_body :=
  jointProof% Solidity.Backend.Scalar.int_mod_body [
    (i0),
    (i1),
    (by decide +kernel),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.int_div_exception
theorem witness_int_div_exception : jointType% Solidity.Backend.Scalar.int_div_exception :=
  jointProof% Solidity.Backend.Scalar.int_div_exception [
    (minimumInt),
    (ineg1),
    (rfl),
    (rfl)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarSignedDivision
