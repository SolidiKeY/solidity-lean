# Readonly bind census and fixture specification

Base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4. Preparation only: no
migration, owner approval or Lean validation is claimed.

| Original declaration | Case and retained observation |
| --- | --- |
| CapturePhases.compose | Five successful phase runs, admission false, actual post-instance state and captured values/bytes. |
| CaptureFailures.target_failed | Receiver halts at s1, before subsequent phases. |
| CaptureFailures.value_failed | Receiver succeeds, value halts at s2. |
| CaptureFailures.arguments_failed | Receiver and value succeed, arguments halt at s3. |
| CaptureFailures.encoding_failed | Earlier phases succeed, encoding halts at s4. |
| CaptureFailures.code_rejected | Phases and lookup succeed, no-code rejection reverts at s5. |
| EnvironmentCredit.known | Known instance and successful credit continue from final state. |
| EnvironmentCredit.unknown | No instance; continue from recorded state without credit. |
| EnvironmentCredit.failed | Known instance and failed credit return the same halt and final state. |
| EnvironmentCredit.callback_credit_failed | Admitted callback, known instance, failed credit; return same halt and final state before callback continuation. |

The halt branch must preserve the state returned by the first computation,
not the original state, and must not run the continuation. The success branch
must run the continuation on the returned state. All original premises, states,
branches, statements and producers remain frozen. These equations do not
establish a callee-body producer, whole-world preservation or native behavior.

Existing controls, not rechecked here: CaptureFailureControls provides
rejected_after_arguments, effect_not_rolled_back, no_callee_events,
receiver_exhaustion and admitted_control. EnvironmentCreditControls provides
static_credit_finishes, storage_kept, unknown_credit_skipped, overflow_halts,
callback_overflow_halts and callback_failure_has_only_attempt.

For remaining failure phases construct inhabited isolated fixtures using actual
typed evaluator inputs; an assumed run equation is not a witness. Include
observable state changes and a distinguishable continuation for both bind
branches, admitted and rejected code, known and unknown instances, and callback
guard acceptance and refusal. Do not claim an original theorem covers a branch
outside its premises. Record each fixture's producer, result and scope. Existing
controls do not establish that all ten cases are inhabited.

Solidity.Source.Hoare.run_bind already states the same equation over the
reducible EMState alias and imports Solidity.Source.Machine. Assess import
direction, exact elaborated statements, timing and dependency cost before
deciding whether to reuse it or introduce an additive shared lemma. Import
compatibility and timing equivalence have not been established.

The census is textual, not a Lean parser. Its synthetic controls are external
Python tests, not kernel proofs; they cannot establish semantic use, statement
equivalence or exhaustiveness under arbitrary Lean syntax. H55 V08/StorageOps
fixtures and Yul capacity_exact are excluded.

Reproduce with `python3 scripts/h62/item1/readonly-bind/census.py` and
`PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item1/readonly-bind/test_census.py`.
The latter passed six controls on 2026-11-06. Independent finder and skeptic
reviews and Lean checks remain pending; this preparation is not a milestone
acceptance. Exact-file RO agreement is requested for all three original files
listed above before edits.
