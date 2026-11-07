import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Environment.Composition

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.EnvironmentComposition
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Environment.runSlice_append
theorem witness_runSlice_append : jointType% Solidity.Backend.Environment.runSlice_append :=
  jointProof% Solidity.Backend.Environment.runSlice_append [
    (Solidity.Backend.Environment.sample),
    ([]),
    ([]),
    (targetSlice)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.sliceStep_crypto
theorem witness_sliceStep_crypto : jointType% Solidity.Backend.Environment.sliceStep_crypto :=
  jointProof% Solidity.Backend.Environment.sliceStep_crypto [
    (Solidity.Backend.Environment.sample),
    (.push ⟨0, by decide⟩ #v[]),
    (targetSlice),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.sliceStep_data
theorem witness_sliceStep_data : jointType% Solidity.Backend.Environment.sliceStep_data :=
  jointProof% Solidity.Backend.Environment.sliceStep_data [
    (Solidity.Backend.Environment.sample),
    (.push ⟨0, by decide⟩ #v[]),
    (targetSlice),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.runSlice_crypto
theorem witness_runSlice_crypto : jointType% Solidity.Backend.Environment.runSlice_crypto :=
  jointProof% Solidity.Backend.Environment.runSlice_crypto [
    (Solidity.Backend.Environment.sample),
    ([]),
    (targetSlice),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.runSlice_data
theorem witness_runSlice_data : jointType% Solidity.Backend.Environment.runSlice_data :=
  jointProof% Solidity.Backend.Environment.runSlice_data [
    (Solidity.Backend.Environment.sample),
    ([]),
    (targetSlice),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.keccak_supported
theorem witness_keccak_supported : jointType% Solidity.Backend.Environment.keccak_supported :=
  jointProof% Solidity.Backend.Environment.keccak_supported [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.namespace_supported
theorem witness_namespace_supported : jointType% Solidity.Backend.Environment.namespace_supported :=
  jointProof% Solidity.Backend.Environment.namespace_supported [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (⟨0, by decide⟩)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.materialize_supported
theorem witness_materialize_supported : jointType% Solidity.Backend.Environment.materialize_supported :=
  jointProof% Solidity.Backend.Environment.materialize_supported [
    (0),
    ([1,2])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.slice_select
theorem witness_slice_select : jointType% Solidity.Backend.Environment.slice_select :=
  jointProof% Solidity.Backend.Environment.slice_select [
    (Solidity.Backend.Environment.sample),
    (.msgSender),
    (targetSlice)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.slice_constant
theorem witness_slice_constant : jointType% Solidity.Backend.Environment.slice_constant :=
  jointProof% Solidity.Backend.Environment.slice_constant [
    (Solidity.Backend.Environment.sample),
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (targetSlice)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.source_sequence_failure
theorem witness_source_sequence_failure : jointType% Solidity.Backend.Environment.source_sequence_failure :=
  jointProof% Solidity.Backend.Environment.source_sequence_failure [
    (default),
    ([]),
    ([]),
    ([]),
    (failedStep),
    (failedStep),
    (state0),
    (.revert),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.source_sequence_success
theorem witness_source_sequence_success : jointType% Solidity.Backend.Environment.source_sequence_success :=
  jointProof% Solidity.Backend.Environment.source_sequence_success [
    (default),
    ([]),
    ([]),
    ([]),
    (identityStep),
    (identityStep),
    (state0),
    (initialOut),
    (by first | rfl | decide +kernel)
  ]

end Solidity.Backend.Scalar.H62Audit.EnvironmentComposition
