# Group 02 callable-entry handoff

Final fixture counts: **67 working, 0 broken, 0 blocked; 0 exclusions**.

Every before status below is a fresh reproduction on `006fcd59`, distinct from the historical `cadb628c` evidence. None was already fixed.

The full reports, source hashes, exact pipeline observations and per-fixture command configuration are in [group02.json](group02.json). Exact completion commands are in [group02-init-commands.sh](group02-init-commands.sh). The prior [command transcript](group02-commands.sh) is retained as history; use the new distinct output paths to preserve its reports.

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
| `inheritance/constructor_inheritance_init_order_3_viaIR.sol` | broken | viaIR: working |
| `inheritance/constructor_with_params_inheritance_2.sol` | broken | legacy: working; viaIR: working |
| `inheritance/pass_dynamic_arguments_to_the_base_base_with_gap.sol` | broken | legacy: working; viaIR: working |
| `inheritance/pass_dynamic_arguments_to_the_base_base.sol` | broken | legacy: working; viaIR: working |
| `inheritance/pass_dynamic_arguments_to_the_base.sol` | broken | legacy: working; viaIR: working |
| `inheritance/state_variables_init_order_2.sol` | broken | legacy: working; viaIR: working |
| `inheritance/state_variables_init_order_3.sol` | broken | viaIR: working |
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


At `1d99d00d`, the first entrypoint repair had exposed two initialization-order
mismatches. This completion fixes both without changing their upstream inputs:

- `inheritance/constructor_inheritance_init_order_3_viaIR.sol`: `x()` now returns
  the required `2` (previously `4`). The independent legacy companion still returns `4`.
- `inheritance/state_variables_init_order_3.sol`: all eight observations now match:
  `a=17`, `b=42`, `c=51`, `b_a=17`, `b_b=42`, `b_c=51`, `d=23`, `e=42`.

Verified compiler provenance selects the source construction schedule. Legacy
retains global initialization before base arguments/bodies. ViaIR captures base
arguments first, then interleaves each reverse-C3 owner's initializers and body.
Compiler declaration IDs select ownership, including implicit constructors.
The intrinsic run, constructor helpers, modifier/return handling and checked
assignment operations are unchanged.

Every required pipeline now completes every original observation. The previous
first-mismatch prefixes (and the five then-unobserved calls) remain recorded in
per-case `priorEntryRepairAfter` reports; no earlier evidence was overwritten.
Fresh initialization-before reports for both failures and the legacy companion
are also retained. All 67 original fresh-master reproductions remain broken;
none was already fixed or is an expected exclusion.

| Pipeline | Working | Broken | Blocked |
| --- | ---: | ---: | ---: |
| legacy | 65 | 0 | 0 |
| viaIR | 66 | 0 | 0 |

The completion model SHA-256 is
`4def0e389306e966b857dc45c30fde97248d5b15fced83983c0f416428a93ec6`.
The first repair's `87539855…` reports, timings and hashes are preserved as a
separate phase. The new 67-fixture replay took 442.990 seconds total (median
6.123 seconds, maximum 16.249 seconds); some per-file controls ran concurrently,
so this is not an isolated performance comparison with the prior 1,207.628-second
run. No fuel, heartbeat or process timeout was increased.

Eleven kernel-checked source controls cover arguments, implicit owners,
constructor modifier suffixes and early returns, width refusal, and failure
ordering. All use only `propext`, `Classical.choice` and `Quot.sound`.
The legacy narrow-width control pins the existing model's empty-revert guard,
not the EVM `Panic(0x11)` payload. The exact legacy assert panic versus viaIR
base revert demonstrates that a failed base prevents later IR initialization.
These are concrete typed-run proofs, not a universal compiler/lowering theorem.

At the prior milestone, the managed runtime gate passed: Lean 4.24.0, Lake 5.0.0-src+797c613 and
`lake build Solidity.KeySort`. Its library (649 jobs), compiled TestSuite
(249 jobs), frozen sort and frozen corpus gates pass. The corpus retains all
774 existing obligation rows without verdict/generated-output drift.
TestSuite derivations required a serial retry after concurrent workers hit
the 16 GiB memory boundary; all 21 targets passed with `LEAN_NUM_THREADS=1`
(maximum 129.6 s), with proof limits unchanged. The interrupted log is retained.

The required JavaScript suite passes 14/14; entrypoint controls, replay,
strict automation, layering and reachability pass. The prior affected source-suite
comparison retained 5 passes and 3 failures on both master and patch: one
unsupported stored-function observation and two unchanged 300-second timeouts.
That Node source-suite comparison was not rerun for this initializer-only
follow-up; constructor and inheritance Lean examples were checked fresh.
See [validation evidence](group02-validation.json) for exact commands,
resource blocks, trust/axiom inventory, reviewer findings and long-log paths.
The reviewable patch is on `repair/group02-entrypoints`, based on
`006fcd593f5beeb540e7adf2bc76de4638566924`; nothing was pushed or merged.


Completion verification and final build results are recorded separately in the
updated [validation evidence](group02-validation.json); the complete earlier
validation object remains under `priorMilestoneValidation`. The original patch
and log archive remain at their existing paths; the completed patch is
exported separately as `/workspace/group02-entrypoints-complete.patch`.


Final completion gates all pass: 73 dependency-ordered affected builds followed
by full `run-lean.sh` and frozen corpus verification, 75 successful commands.
The library (649 jobs), TestSuite (249 jobs), frozen sort (377/131) and corpus
(774 unchanged obligation rows) pass. No resource block occurred in this
follow-up. One Lean worker was used; the maximum TestSuite derivation module
time was 215.177 seconds. `OpenLoops` took 734.213 seconds and `PublicGetters`
140.053 seconds. The completed gate manifest retains every command, exit,
duration and log. Unsupported/unported corpus rows are unchanged, not newly
claimed as proved. The implementation commit is `6fceb880`; the final validation
commit follows on the same lane. Nothing was pushed or merged.
