| Module | Its examples |
|---|---|
| `Examples/Benchmark/SolkeyData/ArrayRemoveByShifting.lean` | solkey real-world shift-remove with its bounds clause and concrete `test`; both unknown at the loop leaves. |
| `Examples/Benchmark/SolkeyData/ArrayRemoveByShiftingOpen.lean` | solkey's open variant: full shift specification, unknown (the invariant cannot read the entry state). |
| `Examples/Benchmark/SolkeyData/ArrayReplaceFromEnd.lean` | Swap-with-last removal; length clause and `test` proved, element clauses unknown past `delAt`. |
| `Examples/Benchmark/SolkeyData/Enum.lean` | Enum state variable: `get`, `set`, `cancel`, `reset` obligations proved. |
| `Examples/Benchmark/SolkeyData/IterableMapping.lean` | Struct-of-array-and-mappings with three class invariants; every clause by hand, obligations unknown. |
| `Examples/Benchmark/SolkeyData/NestedMapping.lean` | solkey real-world clauses with the two-key frame; `get` proved, frame cases by hand. |
