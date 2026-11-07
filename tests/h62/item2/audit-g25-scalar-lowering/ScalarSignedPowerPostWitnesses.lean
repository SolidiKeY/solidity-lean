import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.SignedPowerPost

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarSignedPowerPost
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.powerPostTest_correct
theorem witness_powerPostTest_correct : jointType% Solidity.Backend.Scalar.powerPostTest_correct :=
  jointProof% Solidity.Backend.Scalar.powerPostTest_correct [
    (false),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.powerSignBody_correct
theorem witness_powerSignBody_correct : jointType% Solidity.Backend.Scalar.powerSignBody_correct :=
  jointProof% Solidity.Backend.Scalar.powerSignBody_correct [
    (false),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.powerPost_correct
theorem witness_powerPost_correct : jointType% Solidity.Backend.Scalar.powerPost_correct :=
  jointProof% Solidity.Backend.Scalar.powerPost_correct [
    (false),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.powerPostValue_map
theorem witness_powerPostValue_map : jointType% Solidity.Backend.Scalar.powerPostValue_map :=
  jointProof% Solidity.Backend.Scalar.powerPostValue_map [
    (false),
    (u0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.powerPost_source
theorem witness_powerPost_source : jointType% Solidity.Backend.Scalar.powerPost_source :=
  jointProof% Solidity.Backend.Scalar.powerPost_source [
    (default),
    ([]),
    (state0),
    (.simple (.bool false)),
    (.simple (.lit 0 (by decide))),
    (false),
    (u0),
    (by first | rfl | decide +kernel),
    (by first | rfl | decide +kernel)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarSignedPowerPost
