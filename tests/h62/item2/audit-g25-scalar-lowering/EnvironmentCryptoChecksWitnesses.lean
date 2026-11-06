import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Environment.CryptoChecks

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.EnvironmentCryptoChecks
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Environment.intrinsic_hash_control
theorem witness_intrinsic_hash_control : jointType% Solidity.Backend.Environment.intrinsic_hash_control :=
  jointProof% Solidity.Backend.Environment.intrinsic_hash_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.builtin_selection_control
theorem witness_builtin_selection_control : jointType% Solidity.Backend.Environment.builtin_selection_control :=
  jointProof% Solidity.Backend.Environment.builtin_selection_control [
    (.keccak)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.unset_argument_control
theorem witness_unset_argument_control : jointType% Solidity.Backend.Environment.unset_argument_control :=
  jointProof% Solidity.Backend.Environment.unset_argument_control [
    (.keccak)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.byte_normalization_control
theorem witness_byte_normalization_control : jointType% Solidity.Backend.Environment.byte_normalization_control :=
  jointProof% Solidity.Backend.Environment.byte_normalization_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.keccak_bytes_control
theorem witness_keccak_bytes_control : jointType% Solidity.Backend.Environment.keccak_bytes_control :=
  jointProof% Solidity.Backend.Environment.keccak_bytes_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.wrong_preimage_control
theorem witness_wrong_preimage_control : jointType% Solidity.Backend.Environment.wrong_preimage_control :=
  jointProof% Solidity.Backend.Environment.wrong_preimage_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.namespace_instruction_control
theorem witness_namespace_instruction_control : jointType% Solidity.Backend.Environment.namespace_instruction_control :=
  jointProof% Solidity.Backend.Environment.namespace_instruction_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.namespace_inhabited
theorem witness_namespace_inhabited : jointType% Solidity.Backend.Environment.namespace_inhabited :=
  jointProof% Solidity.Backend.Environment.namespace_inhabited []

-- AUDIT-WITNESS: Solidity.Backend.Environment.precompile_selection_control
theorem witness_precompile_selection_control : jointType% Solidity.Backend.Environment.precompile_selection_control :=
  jointProof% Solidity.Backend.Environment.precompile_selection_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.malformed_recovery_control
theorem witness_malformed_recovery_control : jointType% Solidity.Backend.Environment.malformed_recovery_control :=
  jointProof% Solidity.Backend.Environment.malformed_recovery_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.recovery_positive
theorem witness_recovery_positive : jointType% Solidity.Backend.Environment.recovery_positive :=
  jointProof% Solidity.Backend.Environment.recovery_positive []

-- AUDIT-WITNESS: Solidity.Backend.Environment.precompile_suffix_bytes
theorem witness_precompile_suffix_bytes : jointType% Solidity.Backend.Environment.precompile_suffix_bytes :=
  jointProof% Solidity.Backend.Environment.precompile_suffix_bytes [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (⟨0, by decide⟩)
  ]

end Solidity.Backend.Scalar.H62Audit.EnvironmentCryptoChecks
