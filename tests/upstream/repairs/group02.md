# Group 02 callable-entry handoff

Final fixture counts: 65 working, 2 broken.

Every before status below is a fresh reproduction on `006fcd59`, distinct from the historical `cadb628c` evidence. None was already fixed.

The full reports, source hashes, exact pipeline observations and per-fixture command configuration are in [group02.json](group02.json). Exact final commands are in [group02-commands.sh](group02-commands.sh).

| Fixture under `test/libsolidity/semanticTests/` | Before | Final pipelines |
| --- | --- | --- |
| `accessor/accessor_for_const_state_variable.sol` | broken | legacy: working; viaIR: working |
| `accessor/accessor_for_state_variable.sol` | broken | legacy: working; viaIR: working |
| `constructor/inline_member_init_inheritence_without_constructor.sol` | broken | legacy: working; viaIR: working |
| `constructor/state_variable_initialization.sol` | broken | legacy: working; viaIR: working |
| `functionCall/inheritance/base_base_overload.sol` | broken | legacy: working; viaIR: working |
| `functionCall/inheritance/base_overload.sol` | broken | legacy: working; viaIR: working |
| `functionCall/inheritance/call_unimplemented_base.sol` | broken | legacy: working; viaIR: working |
| `functionTypes/same_function_in_construction_and_runtime.sol` | broken | legacy: working; viaIR: working |
| `getters/array_mapping_struct.sol` | broken | legacy: working; viaIR: working |
| `getters/arrays.sol` | broken | legacy: working; viaIR: working |
| `getters/mapping_array_struct.sol` | broken | legacy: working; viaIR: working |
| `getters/mapping_to_struct.sol` | broken | legacy: working; viaIR: working |
| `getters/mapping_with_names.sol` | broken | legacy: working; viaIR: working |
| `getters/mapping.sol` | broken | legacy: working; viaIR: working |
| `immutable/assign_from_immutables.sol` | broken | legacy: working; viaIR: working |
| `immutable/delete.sol` | broken | legacy: working; viaIR: working |
| `immutable/getter.sol` | broken | legacy: working; viaIR: working |
| `immutable/small_types_in_reverse.sol` | broken | legacy: working; viaIR: working |
| `inheritance/access_base_storage.sol` | broken | legacy: working; viaIR: working |
| `inheritance/constructor_inheritance_init_order_3_legacy.sol` | broken | legacy: working |
| `inheritance/constructor_inheritance_init_order_3_viaIR.sol` | broken | viaIR: broken |
| `inheritance/constructor_with_params_inheritance_2.sol` | broken | legacy: working; viaIR: working |
| `inheritance/pass_dynamic_arguments_to_the_base_base_with_gap.sol` | broken | legacy: working; viaIR: working |
| `inheritance/pass_dynamic_arguments_to_the_base_base.sol` | broken | legacy: working; viaIR: working |
| `inheritance/pass_dynamic_arguments_to_the_base.sol` | broken | legacy: working; viaIR: working |
| `inheritance/state_variables_init_order_2.sol` | broken | legacy: working; viaIR: working |
| `inheritance/state_variables_init_order_3.sol` | broken | viaIR: broken |
| `inheritance/state_variables_init_order.sol` | broken | legacy: working; viaIR: working |
| `literals/fractional_denominations.sol` | broken | legacy: working; viaIR: working |
| `modifiers/access_through_contract_name.sol` | broken | legacy: working; viaIR: working |
| `modifiers/access_through_module_name.sol` | broken | legacy: working; viaIR: working |
| `modifiers/break_in_modifier.sol` | broken | legacy: working; viaIR: working |
| `modifiers/continue_in_modifier.sol` | broken | legacy: working; viaIR: working |
| `modifiers/function_modifier_calling_functions_in_creation_context.sol` | broken | legacy: working; viaIR: working |
| `modifiers/function_modifier_empty.sol` | broken | legacy: working; viaIR: working |
| `modifiers/function_modifier_for_constructor.sol` | broken | legacy: working; viaIR: working |
| `modifiers/function_modifier_multiple_times_local_vars.sol` | broken | legacy: working; viaIR: working |
| `modifiers/function_modifier_multiple_times.sol` | broken | legacy: working; viaIR: working |
| `modifiers/function_modifier_overriding.sol` | broken | legacy: working; viaIR: working |
| `modifiers/modifer_recursive.sol` | broken | legacy: working; viaIR: working |
| `modifiers/return_does_not_skip_modifier.sol` | broken | legacy: working; viaIR: working |
| `modifiers/return_in_modifier.sol` | broken | legacy: working; viaIR: working |
| `modifiers/stacked_return_with_modifiers.sol` | broken | legacy: working; viaIR: working |
| `operators/shifts/shift_constant_left.sol` | broken | legacy: working; viaIR: working |
| `operators/shifts/shift_constant_right.sol` | broken | legacy: working; viaIR: working |
| `operators/shifts/shift_negative_constant_left.sol` | broken | legacy: working; viaIR: working |
| `operators/shifts/shift_negative_constant_right.sol` | broken | legacy: working; viaIR: working |
| `optimizer/reassigned_reference_storage_alias.sol` | broken | legacy: working; viaIR: working |
| `storage/accessors_mapping_for_array.sol` | broken | legacy: working; viaIR: working |
| `storage/array_accessor.sol` | broken | legacy: working; viaIR: working |
| `storage/simple_accessor.sol` | broken | legacy: working; viaIR: working |
| `storage/struct_accessor.sol` | broken | legacy: working; viaIR: working |
| `structs/struct_named_constructor.sol` | broken | legacy: working; viaIR: working |
| `types/array_mapping_abstract_constructor_param.sol` | broken | legacy: working; viaIR: working |
| `types/mapping_abstract_constructor_param.sol` | broken | legacy: working; viaIR: working |
| `types/mapping_enum_key_v2.sol` | broken | legacy: working; viaIR: working |
| `userDefinedValueType/constant.sol` | broken | legacy: working; viaIR: working |
| `userDefinedValueType/mapping_key.sol` | broken | legacy: working; viaIR: working |
| `userDefinedValueType/wrap_unwrap_via_contract_name.sol` | broken | legacy: working; viaIR: working |
| `variables/public_state_overridding.sol` | broken | legacy: working; viaIR: working |
| `various/inline_member_init_inheritence.sol` | broken | legacy: working; viaIR: working |
| `various/positive_integers_to_signed.sol` | broken | legacy: working; viaIR: working |
| `various/single_copy_with_multiple_inheritance.sol` | broken | legacy: working; viaIR: working |
| `viaYul/mapping_enum_key_getter.sol` | broken | legacy: working; viaIR: working |
| `viaYul/virtual_functions.sol` | broken | legacy: working; viaIR: working |
| `virtualFunctions/internal_virtual_function_calls.sol` | broken | legacy: working; viaIR: working |
| `virtualFunctions/virtual_function_calls.sol` | broken | legacy: working; viaIR: working |


The two remaining failures are initialization-order observations, not missing
entries or matching expected failures:

- `inheritance/constructor_inheritance_init_order_3_viaIR.sol`: `x()` returns
  `4`; upstream requires `2`. The legacy companion passes.
- `inheritance/state_variables_init_order_3.sol`: `a() = 17` and `b() = 42`
  match, then `c()` returns `126`; upstream requires `51`.

There are 131 required pipeline results: 129 working and two broken, both
via-IR. No assigned fixture is excluded or blocked, and none was already fixed
at the original adapter boundary. The command transcript returns nonzero while
these two mismatches remain. Pipeline-specific constructor/initializer ordering
is an integration dependency; this patch does not change its expected results
or substitute an entrypoint that happens to produce them.

The final fixture run took 1,207.628 seconds in total (median 16.952 seconds,
maximum 33.252 seconds per fixture), while full builds/source suites also ran.
Before timings are not a meaningful execution comparison: the old adapter
stopped before the missing calls. Frontend compilation retained the existing
body memoization and segmented compilation; the contract reader built in about
16 seconds before and after the narrow entrypoint change. These are not isolated
performance measurements. No fuel, heartbeat or process limit was increased.

Broken reports retain the existing first-mismatch stop policy. In the state
initialization case, the later five calls are unobserved and are not counted
as matches. Every original expectation line is retained in the evidence JSON
and byte-preserved archive; all observations of each passing fixture are present.

| Pipeline | Working | Broken | Blocked |
| --- | ---: | ---: | ---: |
| legacy | 65 | 0 | 0 |
| viaIR | 64 | 2 | 0 |


The managed runtime gate passes: Lean 4.24.0, Lake 5.0.0-src+797c613 and
`lake build Solidity.KeySort`. Final library (649 jobs), compiled TestSuite
(249 jobs), frozen sort and frozen corpus gates pass. The corpus retains all
774 existing obligation rows without verdict/generated-output drift.
TestSuite derivations required a serial retry after concurrent workers hit
the 16 GiB memory boundary; all 21 targets passed with `LEAN_NUM_THREADS=1`
(maximum 129.6 s), with proof limits unchanged. The interrupted log is retained.

The required JavaScript suite passes 14/14; entrypoint controls, replay,
strict automation, layering and reachability pass. A separate affected source
suite reproduces the same 5 passes and 3 failures on master and patch: one
unsupported stored-function observation and two unchanged 300-second timeouts.
See [validation evidence](group02-validation.json) for exact commands,
resource blocks, trust/axiom inventory, reviewer findings and long-log paths.
The reviewable patch is on `repair/group02-entrypoints`, based on
`006fcd593f5beeb540e7adf2bc76de4638566924`; nothing was pushed or merged.
