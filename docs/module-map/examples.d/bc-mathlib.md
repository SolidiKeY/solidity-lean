| Module | Its examples |
|---|---|
| `Examples/Benchmark/MathLib/Average.lean` | OpenZeppelin v4.9.6 `Math.average` (`(a & b) + (a ^ b) / 2`): exact floor-average target, overflow-free form. Unknown: bitwise carry identity over `uintBitwise` missing. |
| `Examples/Benchmark/MathLib/CeilDiv.lean` | OpenZeppelin v4.9.6 `Math.ceilDiv`: exact ceiling by quotient and remainder. Unknown: division/remainder closer for a symbolic divisor missing. |
| `Examples/Benchmark/MathLib/Log2.lean` | OpenZeppelin v4.9.6 `Math.log2` (eight unchecked shift steps): natural `2^r <= v < 2^(r+1)` as a Lean `NaturalSpec`. Unknown: no `**`/`>>` in clauses; eight joined conditional updates exceed `sol_close_ite_split`'s six. |
| `Examples/Benchmark/MathLib/MinMax.lean` | OpenZeppelin v4.9.6 `max`/`min` and Solady v0.1.0 `clamp` (branchless select as conditionals): all three proved. |
| `Examples/Benchmark/MathLib/MulDiv64.lean` | OpenZeppelin v4.9.6 `mulDiv` contract for `uint64` operands (plain full-precision product, overflowing result reverts): exact floor quotient proved. |
| `Examples/Benchmark/MathLib/Saturating.lean` | OpenZeppelin v5.4.0 `saturatingAdd`/`saturatingSub` (helpers inlined, branchless arithmetic kept): `saturatingSub` proved. `saturatingAdd` unknown: xor-select closer missing. |
| `Examples/Benchmark/MathLib/SignedAbs.lean` | OpenZeppelin v4.9.6 `SignedMath.abs` and checked negation at `type(int256).min`: `neg` proved; kernel runs show `abs(min) = 2^255` and `neg(min)` halting. `abs` clause unknown: no `int`/`uint` comparison in clauses. |
| `Examples/Benchmark/MathLib/Sqrt.lean` | Uniswap v2-core Babylonian `Math.sqrt` with loop invariant and variant: exact floor-root target. Unknown: the `y <= 3` leaf closes; the loop leaves need a nonlinear floor-division closer. |
