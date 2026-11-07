| `Lowering/P9/BoundRecognizer.lean` | Executable sound recognizers (`readyB`, `boundB`, fuelled `finiteDefaultB`) and `catalogueB`, which implies `BoundMemoryCatalogue` from the actual dispatch target and body; `OpsOK` from elaboration. |
| `Lowering/P9/BoundRecognizerControls.lean` | `catalogueB` replaces two hand-built catalogue proofs on elaborated units; refuses zero default fuel and an undeclared function. |

| `Lowering/P9/DefaultRecognizerCompleteness.lean` | Monotonic and existential fuel completeness for the finite-default component only; common fuel for finite lists. |
| `Lowering/P9/DefaultRecognizerControls.lean` | Nested fixed-array and actual struct-layout acceptance, insufficient-fuel controls, larger/shared fuel. |
