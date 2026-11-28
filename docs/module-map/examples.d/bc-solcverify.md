| Module | Its examples |
|---|---|
| `Examples/Benchmark/SolcVerify/CaseAnalysisSimple.lean` | solc-verify case-analysis postconditions on signed storage; correct proved, wrong default refuted (`sol_refute`). |
| `Examples/Benchmark/SolcVerify/DoWhile.lean` | solc-verify `do … while` invariants; all four unknown (invariant not inductive, or needs an inferred bound). |
| `Examples/Benchmark/SolcVerify/LoopInvar.lean` | solc-verify loop invariants with `assert`; two proved, two refuted (`sol_refute`), `forLoop` unknown. |
| `Examples/Benchmark/SolcVerify/OldExpr.lean` | solc-verify `\old` postconditions on owner and counters; incorrect owner change refuted (`sol_refute`). |
| `Examples/Benchmark/SolcVerify/OverflowSpec.lean` | solc-verify `uint8` contract invariant `x == y + 1`; `inc` proved, `set` refuted by `sol_refute` (overflow in the clause). |
| `Examples/Benchmark/SolcVerify/Simple.lean` | solc-verify contract invariant `x == y`; `add`, constructor and `add_incorrect_2` (call inlined, no entry invariant owed) proved, `add_incorrect` refuted (`sol_refute`). |
| `Examples/Benchmark/SolcVerify/Storage.lean` | solc-verify records in a mapping of structs; frame (`modifies`) and postconditions all proved. |
| `Examples/Benchmark/SolcVerify/StructMapping.lean` | SMTChecker `struct_1`: a struct stored in a mapping agrees with its memory copy; proved. |
