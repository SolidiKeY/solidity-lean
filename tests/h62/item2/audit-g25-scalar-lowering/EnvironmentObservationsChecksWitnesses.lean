import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Environment.ObservationsChecks

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.EnvironmentObservationsChecks
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Environment.sample_observations
theorem witness_sample_observations : jointType% Solidity.Backend.Environment.sample_observations :=
  jointProof% Solidity.Backend.Environment.sample_observations []

-- AUDIT-WITNESS: Solidity.Backend.Environment.represented_ok
theorem witness_represented_ok : jointType% Solidity.Backend.Environment.represented_ok :=
  jointProof% Solidity.Backend.Environment.represented_ok [
    (default),
    ([]),
    (state0),
    (Solidity.Backend.Environment.sample)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.inhabited_certificate
theorem witness_inhabited_certificate : jointType% Solidity.Backend.Environment.inhabited_certificate :=
  jointProof% Solidity.Backend.Environment.inhabited_certificate [
    (.msgSender),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.high_address_control
theorem witness_high_address_control : jointType% Solidity.Backend.Environment.high_address_control :=
  jointProof% Solidity.Backend.Environment.high_address_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.high_balance_control
theorem witness_high_balance_control : jointType% Solidity.Backend.Environment.high_balance_control :=
  jointProof% Solidity.Backend.Environment.high_balance_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.own_balance_control
theorem witness_own_balance_control : jointType% Solidity.Backend.Environment.own_balance_control :=
  jointProof% Solidity.Backend.Environment.own_balance_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.wrong_opcode_control
theorem witness_wrong_opcode_control : jointType% Solidity.Backend.Environment.wrong_opcode_control :=
  jointProof% Solidity.Backend.Environment.wrong_opcode_control []

end Solidity.Backend.Scalar.H62Audit.EnvironmentObservationsChecks
