import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: min, max, clamp

Sources: OpenZeppelin Contracts v4.9.6, `Math.max` and `Math.min`,
<https://github.com/OpenZeppelin/openzeppelin-contracts/blob/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/utils/math/Math.sol#L16-L28>; Solady v0.1.0, `FixedPointMathLib.clamp`,
<https://github.com/Vectorized/solady/blob/21202175063a0010826bf42697b5aa2ff0c27f9f/src/utils/FixedPointMathLib.sol#L1083-L1094>.

Changes: `public` instead of `internal` and the `@custom:key` clauses.
`min` and `max` are the source's. Solady's `clamp` is branchless assembly,
`z := xor(x, mul(xor(x, minValue), gt(minValue, x)))` then the same with
`maxValue` and `lt(maxValue, z)`; each `xor/mul` line selects
`gt(minValue, x) ? minValue : x` (resp. `lt(maxValue, z) ? maxValue : z`),
written here as those two conditionals, with the named return `z`.

Natural specifications: `max` and `min` bound both arguments and return
one of them. `clamp` lies in `[minValue, maxValue]` when that interval is
nonempty, is the identity inside it, returns `minValue` below it, and
returns `maxValue` above `maxValue` (also when the interval is empty, as
the source does).
-/
namespace Solidity.Examples.Benchmark.MathLib.MinMax

def MinMax : Contract := contract!{
  ensures \result >= a && \result >= b;
  ensures \result == a || \result == b;
  function max(uint256 a, uint256 b) public pure returns (uint256) {
    return a > b ? a : b;
  }
  ensures \result <= a && \result <= b;
  ensures \result == a || \result == b;
  function min(uint256 a, uint256 b) public pure returns (uint256) {
    return a < b ? a : b;
  }
  ensures minValue <= maxValue -> minValue <= z && z <= maxValue;
  ensures minValue <= x && x <= maxValue -> z == x;
  ensures x < minValue && minValue <= maxValue -> z == minValue;
  ensures maxValue < x -> z == maxValue;
  function clamp(uint256 x, uint256 minValue, uint256 maxValue) public pure returns (uint256 z) {
    z = x < minValue ? minValue : x;
    z = maxValue < z ? maxValue : z;
  }
}
local instance : InContract := ⟨MinMax⟩
open scoped Scoped

/-- `max`: an upper bound of both arguments, and one of them. -/
theorem spec_max : ⊢ spec!{ max } := by sol_prove <;> (sol_leaf; sol_close)
/-- `min`: a lower bound of both arguments, and one of them. -/
theorem spec_min : ⊢ spec!{ min } := by sol_prove <;> (sol_leaf; sol_close)
/-- `clamp`: in range, identity inside, saturating at either end. -/
theorem spec_clamp : ⊢ spec!{ clamp } := by sol_prove <;> (sol_leaf; sol_close)

end Solidity.Examples.Benchmark.MathLib.MinMax
