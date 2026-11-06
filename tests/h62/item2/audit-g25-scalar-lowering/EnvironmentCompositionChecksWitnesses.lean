import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Environment.CompositionChecks

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.EnvironmentCompositionChecks
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Environment.mixed_observation_control
theorem witness_mixed_observation_control : jointType% Solidity.Backend.Environment.mixed_observation_control :=
  jointProof% Solidity.Backend.Environment.mixed_observation_control [
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.materialize_then_hash
theorem witness_materialize_then_hash : jointType% Solidity.Backend.Environment.materialize_then_hash :=
  jointProof% Solidity.Backend.Environment.materialize_then_hash [
    (Solidity.Backend.Environment.sample),
    (emptyMemory),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.source_effect_control
theorem witness_source_effect_control : jointType% Solidity.Backend.Environment.source_effect_control :=
  jointProof% Solidity.Backend.Environment.source_effect_control [
    (default),
    (localState)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.source_order_control
theorem witness_source_order_control : jointType% Solidity.Backend.Environment.source_order_control :=
  jointProof% Solidity.Backend.Environment.source_order_control [
    (default),
    ([]),
    (state0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.source_order_distinguishes
theorem witness_source_order_distinguishes : jointType% Solidity.Backend.Environment.source_order_distinguishes :=
  jointProof% Solidity.Backend.Environment.source_order_distinguishes [
    (default),
    ([]),
    (state0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.opcode_order_control
theorem witness_opcode_order_control : jointType% Solidity.Backend.Environment.opcode_order_control :=
  jointProof% Solidity.Backend.Environment.opcode_order_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.repeated_balance_control
theorem witness_repeated_balance_control : jointType% Solidity.Backend.Environment.repeated_balance_control :=
  jointProof% Solidity.Backend.Environment.repeated_balance_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.forced_credit_counterexample
theorem witness_forced_credit_counterexample : jointType% Solidity.Backend.Environment.forced_credit_counterexample :=
  jointProof% Solidity.Backend.Environment.forced_credit_counterexample []

-- AUDIT-WITNESS: Solidity.Backend.Environment.changed_time_counterexample
theorem witness_changed_time_counterexample : jointType% Solidity.Backend.Environment.changed_time_counterexample :=
  jointProof% Solidity.Backend.Environment.changed_time_counterexample []

end Solidity.Backend.Scalar.H62Audit.EnvironmentCompositionChecks
