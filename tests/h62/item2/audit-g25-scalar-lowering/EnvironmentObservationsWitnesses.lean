import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Environment.Observations

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.EnvironmentObservations
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Environment.account_value
theorem witness_account_value : jointType% Solidity.Backend.Environment.account_value :=
  jointProof% Solidity.Backend.Environment.account_value [
    (u0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.account_address
theorem witness_account_address : jointType% Solidity.Backend.Environment.account_address :=
  jointProof% Solidity.Backend.Environment.account_address [
    (Solidity.Backend.Environment.account u0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.select_correct
theorem witness_select_correct : jointType% Solidity.Backend.Environment.select_correct :=
  jointProof% Solidity.Backend.Environment.select_correct [
    (Solidity.Backend.Environment.sample),
    (.msgSender),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.balance_correct
theorem witness_balance_correct : jointType% Solidity.Backend.Environment.balance_correct :=
  jointProof% Solidity.Backend.Environment.balance_correct [
    (Solidity.Backend.Environment.sample),
    (u0),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.balance_address
theorem witness_balance_address : jointType% Solidity.Backend.Environment.balance_address :=
  jointProof% Solidity.Backend.Environment.balance_address [
    (Solidity.Backend.Environment.sample),
    (Solidity.Backend.Environment.account u0),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.own_balance
theorem witness_own_balance : jointType% Solidity.Backend.Environment.own_balance :=
  jointProof% Solidity.Backend.Environment.own_balance [
    (Solidity.Backend.Environment.sample),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.world_balance
theorem witness_world_balance : jointType% Solidity.Backend.Environment.world_balance :=
  jointProof% Solidity.Backend.Environment.world_balance [
    (Unit),
    (fun _ => default),
    (sampleWorld),
    (Solidity.Backend.Environment.sample),
    (by first | rfl | decide +kernel),
    (u0),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.Represents.denote
theorem witness_Represents_denote : jointType% Solidity.Backend.Environment.Represents.denote :=
  jointProof% Solidity.Backend.Environment.Represents.denote [
    (default),
    ([]),
    (Solidity.Backend.Environment.sample),
    (representedState),
    (representedProof),
    (.msgSender)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.intrinsic_correct
theorem witness_intrinsic_correct : jointType% Solidity.Backend.Environment.intrinsic_correct :=
  jointProof% Solidity.Backend.Environment.intrinsic_correct [
    (default),
    ([]),
    (Solidity.Backend.Environment.sample),
    (representedState),
    (representedProof),
    (.msgSender),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.selected_bytes
theorem witness_selected_bytes : jointType% Solidity.Backend.Environment.selected_bytes :=
  jointProof% Solidity.Backend.Environment.selected_bytes []

-- AUDIT-WITNESS: Solidity.Backend.Environment.balance_bytes
theorem witness_balance_bytes : jointType% Solidity.Backend.Environment.balance_bytes :=
  jointProof% Solidity.Backend.Environment.balance_bytes []

-- AUDIT-WITNESS: Solidity.Backend.Environment.balance_underflow
theorem witness_balance_underflow : jointType% Solidity.Backend.Environment.balance_underflow :=
  jointProof% Solidity.Backend.Environment.balance_underflow [
    (Solidity.Backend.Environment.sample)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.refused_fields
theorem witness_refused_fields : jointType% Solidity.Backend.Environment.refused_fields :=
  jointProof% Solidity.Backend.Environment.refused_fields [
    (Solidity.Backend.Environment.sample),
    ([u99])
  ]

end Solidity.Backend.Scalar.H62Audit.EnvironmentObservations
