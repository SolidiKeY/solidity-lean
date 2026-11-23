| `Correctness/Lowering/Sim/Coverage/Obstruction.lean` | Exact accepted empty production run under `elabKernelTotal` refuting frozen v1 diagram coverage: placement may use an unrelated context. |
| `Correctness/Lowering/Sim/Coverage/ProductionV2.lean` | Additive caller-placed production and coverage vocabulary, preserving v1 receipts and unchanged acceptance. |
| `Correctness/Lowering/Sim/Coverage/SpellingObstruction.lean` | Exact accepted, caller-placed empty run in an unchecked scope refuting coverage with the frozen spelling relation. |
| `Examples/Lowering/Sim/Coverage.lean` | Checks both coverage obstructions and the versioned receipt projection, plus independent decoding, alignment, actual lowering and program-acceptance facts for the existing smoke. |
| `Correctness/Lowering/Sim/Coverage/Alignment.lean` | Derives an aligned context map from existing Source spelling using the decoder owner’s primitive-locals theorem, independently of the restricted coverage predicate. |
| `Correctness/Lowering/Sim/Coverage/LoweringReceipt.lean` | Converts successful finite lowering derivations into actual standalone lowering receipts, preserving all state; no elaboration-success claim. |
