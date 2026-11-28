| `Examples/Benchmark/SolkeyOz/OZCounters.lean` | solkey's OpenZeppelin `Counters` port: all four clauses proved (unchecked increment/decrement by the leaf closer). |
| `Examples/Benchmark/SolkeyOz/OZMath.lean` | solkey's OpenZeppelin `Math` port: `tryAdd`, `max`, `min` proved; `trySub`, `tryMul`, `tryDiv`, `tryMod`, `average`, `ceilDiv` unknown, each with its stuck leaf and missing closer law. |
| `Examples/Benchmark/SolkeyOz/OZNonces.lean` | solkey's OpenZeppelin `Nonces` port: `nonces`, `useNonce` proved; `useCheckedNonce` unknown (wrapping add with a Boolean `!=` binding). |
| `Examples/Benchmark/SolkeyOz/OZOwnable2Step.lean` | solkey's OpenZeppelin `Ownable2Step` port: all six clauses proved. |
| `Examples/Benchmark/SolkeyOz/OZPausable.lean` | solkey's OpenZeppelin `Pausable` mock port: all six clauses proved. |
| `Examples/Benchmark/SolkeyOz/OZReentrancyGuard.lean` | solkey's OpenZeppelin `ReentrancyGuard` mock port: all five clauses with both contract invariants proved, the recursive re-entry reverting. |
| `Examples/Benchmark/SolkeyOz/SolmateOwned.lean` | solkey's Solmate `Owned` port: both clauses proved. |
