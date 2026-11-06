import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Environment.Metadata

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.EnvironmentMetadata
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Environment.constant_bound
theorem witness_constant_bound : jointType% Solidity.Backend.Environment.constant_bound :=
  jointProof% Solidity.Backend.Environment.constant_bound [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.constant_correct
theorem witness_constant_correct : jointType% Solidity.Backend.Environment.constant_correct :=
  jointProof% Solidity.Backend.Environment.constant_correct [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.truncate_correct
theorem witness_truncate_correct : jointType% Solidity.Backend.Environment.truncate_correct :=
  jointProof% Solidity.Backend.Environment.truncate_correct [
    (⟨0, by decide⟩),
    (0),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.zero_extension
theorem witness_zero_extension : jointType% Solidity.Backend.Environment.zero_extension :=
  jointProof% Solidity.Backend.Environment.zero_extension [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (0),
    (by first | rfl | decide +kernel),
    (by first | rfl | decide +kernel),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.selector_correct
theorem witness_selector_correct : jointType% Solidity.Backend.Environment.selector_correct :=
  jointProof% Solidity.Backend.Environment.selector_correct [
    (⟨0, by decide⟩),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.selector_alignment
theorem witness_selector_alignment : jointType% Solidity.Backend.Environment.selector_alignment :=
  jointProof% Solidity.Backend.Environment.selector_alignment [
    (⟨0, by decide⟩)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.selector_abi_bytes
theorem witness_selector_abi_bytes : jointType% Solidity.Backend.Environment.selector_abi_bytes :=
  jointProof% Solidity.Backend.Environment.selector_abi_bytes [
    (⟨0, by decide⟩)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.address_correct
theorem witness_address_correct : jointType% Solidity.Backend.Environment.address_correct :=
  jointProof% Solidity.Backend.Environment.address_correct [
    (Solidity.Backend.Environment.account u0),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.function_projections
theorem witness_function_projections : jointType% Solidity.Backend.Environment.function_projections :=
  jointProof% Solidity.Backend.Environment.function_projections [
    (Solidity.Backend.Environment.account u0),
    (⟨0, by decide⟩)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.function_correct
theorem witness_function_correct : jointType% Solidity.Backend.Environment.function_correct :=
  jointProof% Solidity.Backend.Environment.function_correct [
    (Solidity.Backend.Environment.account u0),
    (⟨0, by decide⟩),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.declaration_correct
theorem witness_declaration_correct : jointType% Solidity.Backend.Environment.declaration_correct :=
  jointProof% Solidity.Backend.Environment.declaration_correct [
    (resolvedDecl),
    (⟨0, by decide⟩),
    (by first | rfl | decide +kernel),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.typed_constant_correct
theorem witness_typed_constant_correct : jointType% Solidity.Backend.Environment.typed_constant_correct :=
  jointProof% Solidity.Backend.Environment.typed_constant_correct [
    (.bool),
    (true),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.typed_literal_intrinsic
theorem witness_typed_literal_intrinsic : jointType% Solidity.Backend.Environment.typed_literal_intrinsic :=
  jointProof% Solidity.Backend.Environment.typed_literal_intrinsic [
    (default),
    ([]),
    (state0),
    (.uint),
    (0),
    (by first | rfl | decide +kernel),
    ([u99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.selector_intrinsic
theorem witness_selector_intrinsic : jointType% Solidity.Backend.Environment.selector_intrinsic :=
  jointProof% Solidity.Backend.Environment.selector_intrinsic [
    (default),
    ([]),
    (state0),
    (⟨0, by decide⟩),
    ([u99])
  ]

end Solidity.Backend.Scalar.H62Audit.EnvironmentMetadata
