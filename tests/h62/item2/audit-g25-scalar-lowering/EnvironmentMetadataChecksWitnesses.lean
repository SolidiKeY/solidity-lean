import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Environment.MetadataChecks

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.EnvironmentMetadataChecks
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Environment.declaration_selection
theorem witness_declaration_selection : jointType% Solidity.Backend.Environment.declaration_selection :=
  jointProof% Solidity.Backend.Environment.declaration_selection []

-- AUDIT-WITNESS: Solidity.Backend.Environment.missing_metadata_refused
theorem witness_missing_metadata_refused : jointType% Solidity.Backend.Environment.missing_metadata_refused :=
  jointProof% Solidity.Backend.Environment.missing_metadata_refused []

-- AUDIT-WITNESS: Solidity.Backend.Environment.selector_opcode_bytes
theorem witness_selector_opcode_bytes : jointType% Solidity.Backend.Environment.selector_opcode_bytes :=
  jointProof% Solidity.Backend.Environment.selector_opcode_bytes []

-- AUDIT-WITNESS: Solidity.Backend.Environment.selector_abi_opcode_bytes
theorem witness_selector_abi_opcode_bytes : jointType% Solidity.Backend.Environment.selector_abi_opcode_bytes :=
  jointProof% Solidity.Backend.Environment.selector_abi_opcode_bytes []

-- AUDIT-WITNESS: Solidity.Backend.Environment.wrong_alignment_control
theorem witness_wrong_alignment_control : jointType% Solidity.Backend.Environment.wrong_alignment_control :=
  jointProof% Solidity.Backend.Environment.wrong_alignment_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.address_opcode_bytes
theorem witness_address_opcode_bytes : jointType% Solidity.Backend.Environment.address_opcode_bytes :=
  jointProof% Solidity.Backend.Environment.address_opcode_bytes []

-- AUDIT-WITNESS: Solidity.Backend.Environment.packed_function_control
theorem witness_packed_function_control : jointType% Solidity.Backend.Environment.packed_function_control :=
  jointProof% Solidity.Backend.Environment.packed_function_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.truncation_control
theorem witness_truncation_control : jointType% Solidity.Backend.Environment.truncation_control :=
  jointProof% Solidity.Backend.Environment.truncation_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.metadata_width_controls
theorem witness_metadata_width_controls : jointType% Solidity.Backend.Environment.metadata_width_controls :=
  jointProof% Solidity.Backend.Environment.metadata_width_controls []

-- AUDIT-WITNESS: Solidity.Backend.Environment.name_bytes_control
theorem witness_name_bytes_control : jointType% Solidity.Backend.Environment.name_bytes_control :=
  jointProof% Solidity.Backend.Environment.name_bytes_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.byte_store_opcode_control
theorem witness_byte_store_opcode_control : jointType% Solidity.Backend.Environment.byte_store_opcode_control :=
  jointProof% Solidity.Backend.Environment.byte_store_opcode_control []

-- AUDIT-WITNESS: Solidity.Backend.Environment.signed_metadata_control
theorem witness_signed_metadata_control : jointType% Solidity.Backend.Environment.signed_metadata_control :=
  jointProof% Solidity.Backend.Environment.signed_metadata_control []

end Solidity.Backend.Scalar.H62Audit.EnvironmentMetadataChecks
