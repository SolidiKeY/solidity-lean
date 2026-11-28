| Module | Its examples |
|---|---|
| `Examples/Benchmark/MemoryAlgorithms/ArrayEquals.lean` | Equality of two memory arrays; result iff equal lengths and elements (unknown: quantified step leaf). |
| `Examples/Benchmark/MemoryAlgorithms/BubbleSort.lean` | In-place bubble sort of at most eight elements; sortedness clauses, full permutation target (unknown: memory-write loop frame). |
| `Examples/Benchmark/MemoryAlgorithms/CountOccurrences.lean` | Occurrences of a key; exact counting target retained pending a counting aggregate. |
| `Examples/Benchmark/MemoryAlgorithms/Dedupe.lean` | Distinct values of a sorted array into a caller's array; increasing and covering clauses (unknown: memory-write loop frame). |
| `Examples/Benchmark/MemoryAlgorithms/IsSorted.lean` | Adjacent-pair sortedness scan; result iff every adjacent pair is ordered (unknown: quantified step leaf). |
| `Examples/Benchmark/MemoryAlgorithms/PairSum.lean` | Two-pointer pair sum on a sorted array; result iff two positions sum to the target (unknown: existential leaf). |
| `Examples/Benchmark/MemoryAlgorithms/PrefixSums.lean` | Prefix sums into a caller's array; zero entry and recurrence clauses (unknown: memory-write loop frame). |
| `Examples/Benchmark/MemoryAlgorithms/Rotate.lean` | Rotation by k into a caller's array; placement clause (unknown: memory-write loop frame). |
