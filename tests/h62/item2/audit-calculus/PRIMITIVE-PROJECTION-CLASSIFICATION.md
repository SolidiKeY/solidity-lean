# Primitive return validation and projection premises

This covers all six frozen theorem candidates in `Solidity/Semantics/PrimitiveReturnProjection.lean`; source bytes match frozen and adopted master. The file's Declaration/Projection/consume definitions are read as dependencies, not additional frozen theorem rows. Semantic ownership remains unresolved; no migration owner or Calculus ownership rule is substituted.

`Declaration types` carries intrinsic context/binders and the primitive signature equality. `Projection` supports binding every result in the same context or discarding every result, not arbitrary partial selection. `consume` decodes the whole declaration before projecting the successfully decoded environment. These certificates and choices remain typed parameters; no enum/nominal erasure or source default is introduced.

| Theorem | Joint premises and exact conclusion |
| --- | --- |
| `declared_failure` | Actual declared decoder failure on the same bytes propagates the same error through consume, even for discard. No decoder failure is constructed. |
| `declared_success` | Actual declared decoder success yields the projected actual values and the same decoded word tail. No arbitrary projected environment is supplied. |
| `success_validates_declaration` | Actual consume success yields witnesses for successful full declared decoding and equality of the result to the projected values plus that decoded tail. It does not establish success for arbitrary input. |
| `decode_names` | Any two binder sets of the same intrinsic context decode any supplied word list identically. Names vary; primitive context/types do not. This is not a theorem across different signatures. |
| `success_reads_actual_words` | Actual consume success yields a word list read from the original bytes using the declared context length, and successful caller decoding of those same words into the returned environment. The existential caller-decoder tail need not equal the consume result's tail; discard leaves the entire word list unused by the caller, after declared validation. |
| `success_complete_word` | Actual consume success and `i < declared.context.length` imply `i*32+32 ≤ bytes.length`, even when results are discarded. With zero declared words there is no valid demanded index. |

The underlying complete-word read checks required length before the existing ABI load can zero-pad. Primitive word conversions validate the declaration, but surplus bytes, including an incomplete trailing word, may be ignored. No theorem here claims exact input length, empty residual tails, contextual nominal validation or arbitrary-word substitution for the actual bytes. Binder-name invariance and existing existential consequences do not supply source-call, frame or native provenance. The operational O1 consumer remains separate and unfinished.

At checkpoint V139 the exact six ledger bindings are published at private commit 13b8731cd6ec9a68cbfc334f317ef8db2ccd2e28, directory evidence/solidity-h28-sol-20261104/automation-benchmark/primitive-projection-inputs-v139. The pinned census contains 1701 reviewed/3582 pending of5283; prior1695 rows, owner map, scope and provenance are unchanged. Owners remain3884 confirmed/1399 unresolved. This is static classification only, with zero fresh joint witnesses.

No source, statement, dependent definition, interface, budget, axiom, exclusion or toolchain changes. Zero fresh joint witnesses and no fresh Lean/kernel/replay/compiler/runtime/performance acceptance. H28 actualCallerFields/extractionActuallyChanges/replay remains paused and all existing STOPs remain. Historical unavailable exact bytes remain UNVERIFIABLE.
