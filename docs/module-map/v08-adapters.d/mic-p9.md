| `Lowering/P9/BoundRecognizer.lean` | Executable sound recognizers (`readyB`, `boundB`, fuelled `finiteDefaultB`) and `catalogueB`, which implies `BoundMemoryCatalogue` from the actual dispatch target and body; `OpsOK` from elaboration. |
| `Lowering/P9/BoundRecognizerControls.lean` | `catalogueB` replaces two hand-built catalogue proofs on elaborated units; refuses zero default fuel and an undeclared function. |

| `Lowering/P9/DefaultRecognizerCompleteness.lean` | Monotonic and existential fuel completeness for the finite-default component only; common fuel for finite lists. |
| `Lowering/P9/DefaultRecognizerControls.lean` | Nested fixed-array and actual struct-layout acceptance, insufficient-fuel controls, larger/shared fuel. |

| `Lowering/P9/BodyRecognizerCompleteness.lean` | Existing readiness certificates imply their Boolean body checks; no new syntax admitted. |
| `Lowering/P9/CatalogueRecognizerCompleteness.lean` | Entry/catalogue fuel monotonicity and relative completeness up to existential recognizer fuel, with original converse premises. |
| `Lowering/P9/CatalogueCompletenessControls.lean` | Reference/unchecked and existing elaborated-unit controls, checked calls, inadequate-fuel distinction and all-fuel refusal. |
| `Backend/FailurePaths/StorageEncoderTimeout.lean` | Storage-read encoder/local ABI timeout with complete state; no admitted custom-error/compiler claim. |
| `Backend/FailurePaths/StorageEncoderTimeoutControls.lean` | Seeded timeout/completion, both pipelines, memory error signature and storage refusal. |
