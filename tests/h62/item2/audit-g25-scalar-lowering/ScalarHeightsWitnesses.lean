import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Heights

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarHeights
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.duplicate_length
theorem witness_duplicate_length : jointType% Solidity.Backend.Scalar.duplicate_length :=
  jointProof% Solidity.Backend.Scalar.duplicate_length [
    (0),
    ([99]),
    ([99,99]),
    (rfl)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.exchange_length
theorem witness_exchange_length : jointType% Solidity.Backend.Scalar.exchange_length :=
  jointProof% Solidity.Backend.Scalar.exchange_length [
    (0),
    (0),
    ([99]),
    ([0]),
    (99),
    (rfl)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.swap_length
theorem witness_swap_length : jointType% Solidity.Backend.Scalar.swap_length :=
  jointProof% Solidity.Backend.Scalar.swap_length [
    (0),
    ([7,3,99]),
    ([3,7,99]),
    (rfl)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.applyUnary_length
theorem witness_applyUnary_length : jointType% Solidity.Backend.Scalar.applyUnary_length :=
  jointProof% Solidity.Backend.Scalar.applyUnary_length [
    (id),
    ([99]),
    ([99]),
    (rfl)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.applyBinary_length
theorem witness_applyBinary_length : jointType% Solidity.Backend.Scalar.applyBinary_length :=
  jointProof% Solidity.Backend.Scalar.applyBinary_length [
    (fun a _ => a),
    ([7,3]),
    ([7]),
    (rfl)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.applyTernary_length
theorem witness_applyTernary_length : jointType% Solidity.Backend.Scalar.applyTernary_length :=
  jointProof% Solidity.Backend.Scalar.applyTernary_length [
    (fun a _ _ => a),
    ([7,3,2]),
    ([7]),
    (rfl)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.numericStep_height
theorem witness_numericStep_height : jointType% Solidity.Backend.Scalar.numericStep_height :=
  jointProof% Solidity.Backend.Scalar.numericStep_height [
    (.ISZERO),
    ([0]),
    ([1]),
    (rfl)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.step_height
theorem witness_step_height : jointType% Solidity.Backend.Scalar.step_height :=
  jointProof% Solidity.Backend.Scalar.step_height [
    (.op .POP),
    ([99]),
    ([]),
    (rfl)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.run_height
theorem witness_run_height : jointType% Solidity.Backend.Scalar.run_height :=
  jointProof% Solidity.Backend.Scalar.run_height [
    ([]),
    ([99]),
    ([99]),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.stackBound_prefix
theorem witness_stackBound_prefix : jointType% Solidity.Backend.Scalar.stackBound_prefix :=
  jointProof% Solidity.Backend.Scalar.stackBound_prefix [
    ([]),
    ([]),
    (0),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.run_capacity
theorem witness_run_capacity : jointType% Solidity.Backend.Scalar.run_capacity :=
  jointProof% Solidity.Backend.Scalar.run_capacity [
    ([]),
    ([99]),
    ([99]),
    (by first | rfl | decide +kernel),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.prefix_capacity
theorem witness_prefix_capacity : jointType% Solidity.Backend.Scalar.prefix_capacity :=
  jointProof% Solidity.Backend.Scalar.prefix_capacity [
    ([]),
    ([]),
    ([99]),
    ([99]),
    (by first | rfl | decide +kernel),
    (by first | rfl | decide +kernel)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarHeights
