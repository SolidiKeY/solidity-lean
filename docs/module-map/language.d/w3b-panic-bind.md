| `Goals/Panic.lean` | `runCarriesPanicCodes`: conjunction of `panicRunOutcomes`, `panicCodeProvenance` and `panicSourceAssociation` (plan w3b-panic-bind). |
| `Correctness/Panic/Main.lean` | `Semantics.run_panic_codes` assembles the three component proofs; guarded axiom pin permits only `propext`, `Classical.choice` and `Quot.sound`. |
| `Examples/Goals/Panic.lean` | Roadmap pin and example of `runCarriesPanicCodes` proved by `Semantics.run_panic_codes`. |
