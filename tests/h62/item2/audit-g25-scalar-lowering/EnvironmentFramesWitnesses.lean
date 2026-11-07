import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Environment.Frames

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.EnvironmentFrames
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Environment.Stable.observe
theorem witness_Stable_observe : jointType% Solidity.Backend.Environment.Stable.observe :=
  jointProof% Solidity.Backend.Environment.Stable.observe [
    (Solidity.Backend.Environment.sample),
    (Solidity.Backend.Environment.sample),
    (stableSample),
    (.msgSender)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.stable_selection
theorem witness_stable_selection : jointType% Solidity.Backend.Environment.stable_selection :=
  jointProof% Solidity.Backend.Environment.stable_selection [
    (Solidity.Backend.Environment.sample),
    (Solidity.Backend.Environment.sample),
    (stableSample),
    (.msgSender),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.balance_frame
theorem witness_balance_frame : jointType% Solidity.Backend.Environment.balance_frame :=
  jointProof% Solidity.Backend.Environment.balance_frame [
    (Solidity.Backend.Environment.sample),
    (Solidity.Backend.Environment.sample),
    (u0),
    ([u99]),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.ledger_other
theorem witness_ledger_other : jointType% Solidity.Backend.Environment.ledger_other :=
  jointProof% Solidity.Backend.Environment.ledger_other [
    (Solidity.Backend.Environment.sample),
    (Solidity.Backend.Environment.account u1),
    (u0),
    (u0),
    ([u99]),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.self_balance_frame
theorem witness_self_balance_frame : jointType% Solidity.Backend.Environment.self_balance_frame :=
  jointProof% Solidity.Backend.Environment.self_balance_frame [
    (Solidity.Backend.Environment.sample),
    (Solidity.Backend.Environment.sample),
    ([u99]),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.repeated_read
theorem witness_repeated_read : jointType% Solidity.Backend.Environment.repeated_read :=
  jointProof% Solidity.Backend.Environment.repeated_read [
    (Solidity.Backend.Environment.sample),
    (.msgSender),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.repeated_across_stable
theorem witness_repeated_across_stable : jointType% Solidity.Backend.Environment.repeated_across_stable :=
  jointProof% Solidity.Backend.Environment.repeated_across_stable [
    (Solidity.Backend.Environment.sample),
    (Solidity.Backend.Environment.sample),
    (stableSample),
    (.msgSender),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.repeated_balance
theorem witness_repeated_balance : jointType% Solidity.Backend.Environment.repeated_balance :=
  jointProof% Solidity.Backend.Environment.repeated_balance [
    (Solidity.Backend.Environment.sample),
    (Solidity.Backend.Environment.sample),
    (u0),
    ([u99]),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.source_environment_frame
theorem witness_source_environment_frame : jointType% Solidity.Backend.Environment.source_environment_frame :=
  jointProof% Solidity.Backend.Environment.source_environment_frame [
    (default),
    (default),
    ([]),
    ([]),
    (state0),
    (state0),
    (by first | rfl | decide +kernel),
    (by first | rfl | decide +kernel),
    (.msgSender)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.response_table_frame
theorem witness_response_table_frame : jointType% Solidity.Backend.Environment.response_table_frame :=
  jointProof% Solidity.Backend.Environment.response_table_frame [
    (default),
    ([]),
    (state0),
    ([]),
    (.msgSender)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.refuse_non_environment
theorem witness_refuse_non_environment : jointType% Solidity.Backend.Environment.refuse_non_environment :=
  jointProof% Solidity.Backend.Environment.refuse_non_environment [
    (Solidity.Backend.Environment.sample),
    (.GAS),
    ([u99]),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.excluded_constructor_controls
theorem witness_excluded_constructor_controls : jointType% Solidity.Backend.Environment.excluded_constructor_controls :=
  jointProof% Solidity.Backend.Environment.excluded_constructor_controls []

-- AUDIT-WITNESS: Solidity.Backend.Environment.slice_refuses_unsupported
theorem witness_slice_refuses_unsupported : jointType% Solidity.Backend.Environment.slice_refuses_unsupported :=
  jointProof% Solidity.Backend.Environment.slice_refuses_unsupported [
    (Solidity.Backend.Environment.sample),
    (.GAS),
    (targetSlice),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.slice_refusal_controls
theorem witness_slice_refusal_controls : jointType% Solidity.Backend.Environment.slice_refusal_controls :=
  jointProof% Solidity.Backend.Environment.slice_refusal_controls [
    (Solidity.Backend.Environment.sample),
    (targetSlice)
  ]

end Solidity.Backend.Scalar.H62Audit.EnvironmentFrames
