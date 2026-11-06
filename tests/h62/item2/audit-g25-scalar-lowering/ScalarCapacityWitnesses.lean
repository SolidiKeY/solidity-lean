import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Capacity

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarCapacity
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.BinaryInvocation.decode_bytes
theorem witness_BinaryInvocation_decode_bytes : jointType% Solidity.Backend.Scalar.BinaryInvocation.decode_bytes :=
  jointProof% Solidity.Backend.Scalar.BinaryInvocation.decode_bytes [
    (.and),
    (.bool),
    (rfl),
    (booleanAnd),
    (true),
    (true),
    ([99]),
    (⟨by decide +kernel⟩)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.BinaryInvocation.correct
theorem witness_BinaryInvocation_correct : jointType% Solidity.Backend.Scalar.BinaryInvocation.correct :=
  jointProof% Solidity.Backend.Scalar.BinaryInvocation.correct [
    (.and),
    (.bool),
    (rfl),
    (booleanAnd),
    (true),
    (true),
    ([99]),
    (⟨by decide +kernel⟩)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.BinaryInvocation.prefix_safe
theorem witness_BinaryInvocation_prefix_safe : jointType% Solidity.Backend.Scalar.BinaryInvocation.prefix_safe :=
  jointProof% Solidity.Backend.Scalar.BinaryInvocation.prefix_safe [
    (.and),
    (.bool),
    (rfl),
    (booleanAnd),
    (true),
    (true),
    ([99]),
    (⟨by decide +kernel⟩),
    ([]),
    (booleanAnd.code),
    (rfl),
    ([1,1,99]),
    (rfl)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.CheckedInvocation.correct
theorem witness_CheckedInvocation_correct : jointType% Solidity.Backend.Scalar.CheckedInvocation.correct :=
  jointProof% Solidity.Backend.Scalar.CheckedInvocation.correct [
    (.add),
    (.uint),
    (rfl),
    (checkedUintAdd),
    (u255),
    (u1),
    ([99]),
    (checkedAdditionWitness)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.CheckedInvocation.testPrefix_safe
theorem witness_CheckedInvocation_testPrefix_safe : jointType% Solidity.Backend.Scalar.CheckedInvocation.testPrefix_safe :=
  jointProof% Solidity.Backend.Scalar.CheckedInvocation.testPrefix_safe [
    (.add),
    (.uint),
    (rfl),
    (checkedUintAdd),
    (u255),
    (u1),
    ([99]),
    (checkedAdditionWitness),
    ([]),
    (checkedUintAdd.test),
    (rfl),
    ([255,1,99]),
    (rfl)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.ClosedInvocation.prefix_safe
theorem witness_ClosedInvocation_prefix_safe : jointType% Solidity.Backend.Scalar.ClosedInvocation.prefix_safe :=
  jointProof% Solidity.Backend.Scalar.ClosedInvocation.prefix_safe [
    (default),
    ([]),
    (.bool),
    (.simple (.bool true)),
    (boolLiteral true),
    ([99]),
    (⟨by decide +kernel⟩),
    ([]),
    ((boolLiteral (C := default) (Γ := []) true).code),
    (rfl),
    ([99]),
    (rfl)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarCapacity
