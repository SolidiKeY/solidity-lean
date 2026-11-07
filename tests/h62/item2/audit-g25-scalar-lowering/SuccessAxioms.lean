import tests.h62.item2.«audit-g25-scalar-lowering».ScalarTotality
import tests.h62.item2.«audit-g25-scalar-lowering».ClosedTotality
import tests.h62.item2.«audit-g25-scalar-lowering».EnvironmentTotality
import tests.h62.item2.«audit-g25-scalar-lowering».SuccessControls
import tests.h62.item2.«audit-g25-scalar-lowering».BoundaryVectors

/-! Explicit axiom reports for every additive public theorem in checkpoint 3. -/
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.unary_source_isSome
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.binary_source_isSome
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.binary_short_declines
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.unary_source_success
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.binary_source_success
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.unary_certificate_success
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.binary_certificate_success
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.checked_unary_certificate_success
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.checked_binary_certificate_success
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.unary_reject_all_impossible
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.binary_reject_all_impossible
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.checked_unary_reject_all_impossible
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.checked_binary_reject_all_impossible
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.checked_unary_always_revert_impossible
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.checked_binary_always_revert_impossible
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.unary_selection_capacity
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.binary_selection_capacity
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.modular_certificate_success
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.modular_selection_capacity
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.modular_always_revert_impossible
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.uint_div_positive
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.uint_mod_positive
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.int_div_positive
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.int_mod_positive
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.division_components_capacity
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.literal_value
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.literal_code
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.closed_program_success
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.closed_reject_all_impossible
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.supported_closed_unary
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.supported_closed_binary
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.literal_capacity
#print axioms Solidity.Backend.Scalar.H62Audit.Totality.literal_full_stack_refused
#print axioms Solidity.Backend.Scalar.H62Audit.EnvironmentTotality.environment_total
#print axioms Solidity.Backend.Scalar.H62Audit.EnvironmentTotality.environment_never_rejects_all
#print axioms Solidity.Backend.Scalar.H62Audit.EnvironmentTotality.value_certificate_success
#print axioms Solidity.Backend.Scalar.H62Audit.EnvironmentTotality.value_reject_all_impossible
#print axioms Solidity.Backend.Scalar.H62Audit.EnvironmentTotality.values_certificate_success
#print axioms Solidity.Backend.Scalar.H62Audit.EnvironmentTotality.resolved_hash_selection_total
#print axioms Solidity.Backend.Scalar.H62Audit.EnvironmentTotality.resolved_metadata_total
#print axioms Solidity.Backend.Scalar.H62Audit.EnvironmentTotality.nonempty_intrinsic_hash_success
#print axioms Solidity.Backend.Scalar.H62Audit.EnvironmentTotality.every_hash_builtin_selects
#print axioms Solidity.Backend.Scalar.H62Audit.EnvironmentTotality.nonempty_namespace_success
#print axioms Solidity.Backend.Scalar.H62Audit.EnvironmentTotality.observable_failure_boundary
#print axioms Solidity.Backend.Scalar.H62Audit.boolean_not_total
#print axioms Solidity.Backend.Scalar.H62Audit.boolean_and_total
#print axioms Solidity.Backend.Scalar.H62Audit.reject_all_cannot_certify_not
#print axioms Solidity.Backend.Scalar.H62Audit.checked_add_zero_total
#print axioms Solidity.Backend.Scalar.H62Audit.always_revert_cannot_certify_add
#print axioms Solidity.Backend.Scalar.H62Audit.division_failure_observable
#print axioms Solidity.Backend.Scalar.H62Audit.panic_classes_distinct
#print axioms Solidity.Backend.Scalar.H62Audit.physical_capacity_boundary
#print axioms Solidity.Backend.Scalar.H62Audit.gas_and_fork_boundary
#print axioms Solidity.Backend.Scalar.H62Audit.BoundaryVectors.negation_bytes
#print axioms Solidity.Backend.Scalar.H62Audit.BoundaryVectors.push_zero_bytes
