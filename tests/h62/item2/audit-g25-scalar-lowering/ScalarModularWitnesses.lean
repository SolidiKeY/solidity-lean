import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Modular

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarModular
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.uint_word_zero
theorem witness_uint_word_zero : jointType% Solidity.Backend.Scalar.uint_word_zero :=
  jointProof% Solidity.Backend.Scalar.uint_word_zero [
    (u0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.addmod_correct
theorem witness_addmod_correct : jointType% Solidity.Backend.Scalar.addmod_correct :=
  jointProof% Solidity.Backend.Scalar.addmod_correct [
    (u0),
    (u0),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.mulmod_correct
theorem witness_mulmod_correct : jointType% Solidity.Backend.Scalar.mulmod_correct :=
  jointProof% Solidity.Backend.Scalar.mulmod_correct [
    (u0),
    (u0),
    (u0),
    ([99])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarModular
