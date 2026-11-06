import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Environment.Namespace

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.EnvironmentNamespace
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Environment.namespace_preimage
theorem witness_namespace_preimage : jointType% Solidity.Backend.Environment.namespace_preimage :=
  jointProof% Solidity.Backend.Environment.namespace_preimage [
    ([1,2])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.wordBytes_length
theorem witness_wordBytes_length : jointType% Solidity.Backend.Environment.wordBytes_length :=
  jointProof% Solidity.Backend.Environment.wordBytes_length [
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.clearByte_value
theorem witness_clearByte_value : jointType% Solidity.Backend.Environment.clearByte_value :=
  jointProof% Solidity.Backend.Environment.clearByte_value [
    (u0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.root_value
theorem witness_root_value : jointType% Solidity.Backend.Environment.root_value :=
  jointProof% Solidity.Backend.Environment.root_value [
    ([1,2])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.namespace_result
theorem witness_namespace_result : jointType% Solidity.Backend.Environment.namespace_result :=
  jointProof% Solidity.Backend.Environment.namespace_result [
    ([1,2])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.namespace_suffix_correct
theorem witness_namespace_suffix_correct : jointType% Solidity.Backend.Environment.namespace_suffix_correct :=
  jointProof% Solidity.Backend.Environment.namespace_suffix_correct [
    (⟨0, by decide⟩),
    ([1,2]),
    (targetSlice)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.namespace_correct
theorem witness_namespace_correct : jointType% Solidity.Backend.Environment.namespace_correct :=
  jointProof% Solidity.Backend.Environment.namespace_correct [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (targetSlice)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.namespace_source
theorem witness_namespace_source : jointType% Solidity.Backend.Environment.namespace_source :=
  jointProof% Solidity.Backend.Environment.namespace_source [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (targetSlice),
    ([]),
    (emptyNamespaceInput)
  ]

end Solidity.Backend.Scalar.H62Audit.EnvironmentNamespace
