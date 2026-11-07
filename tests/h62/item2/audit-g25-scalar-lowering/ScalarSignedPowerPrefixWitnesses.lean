import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.SignedPowerPrefix

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarSignedPowerPrefix
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.parity_word
theorem witness_parity_word : jointType% Solidity.Backend.Scalar.parity_word :=
  jointProof% Solidity.Backend.Scalar.parity_word [
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.powerNegativePrefix_correct
theorem witness_powerNegativePrefix_correct : jointType% Solidity.Backend.Scalar.powerNegativePrefix_correct :=
  jointProof% Solidity.Backend.Scalar.powerNegativePrefix_correct [
    (i0),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.powerAbsPrefix_correct
theorem witness_powerAbsPrefix_correct : jointType% Solidity.Backend.Scalar.powerAbsPrefix_correct :=
  jointProof% Solidity.Backend.Scalar.powerAbsPrefix_correct [
    (i0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.powerPrepare_correct
theorem witness_powerPrepare_correct : jointType% Solidity.Backend.Scalar.powerPrepare_correct :=
  jointProof% Solidity.Backend.Scalar.powerPrepare_correct [
    (i0),
    (u0),
    ([99])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarSignedPowerPrefix
