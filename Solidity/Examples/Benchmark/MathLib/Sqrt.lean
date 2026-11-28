import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: integer square root (Babylonian method)

Source: Uniswap v2-core, `Math.sqrt`,
<https://github.com/Uniswap/v2-core/blob/ee547b17853e71ed4e0101ccfd52e70d5acded58/contracts/libraries/Math.sol#L10-L22>.

Changes: `public` instead of `internal`, the `@custom:key` clauses, and
`pragma =0.5.16`'s unchecked arithmetic read as 0.8's checked one (no
operation here overflows: `y / 2 + 1 <= 2^255` and `y / x + x` stays below
`2^256` once `x <= y / 2 + 1`). The body is the source's.

Natural specification: `z = ⌊√y⌋`, i.e. `z * z <= y < (z + 1)^2`; the upper
bound is written `y / (z + 1) < z + 1` (equivalent over the naturals) since a
clause's `(z + 1) * (z + 1)` overflows at `y = 2^256 - 1`.

Loop invariant: `z` and `x` are positive, both bound `⌊√y⌋` from above,
and `x` is the Newton step from `z` except before the first iteration. At
exit `x >= z` excludes the initial state (`y / 2 + 1 < y` for `y > 3`),
so `(y / z + z) / 2 >= z`, whence `z * z <= y`. Variant: `z`.
-/
namespace Solidity.Examples.Benchmark.MathLib.Sqrt

def Sqrt : Contract := contract!{
  ensures \result * \result <= y && y / (\result + 1) < \result + 1;
  function sqrt(uint y) public pure returns (uint z) {
    if (y > 3) {
      z = y;
      uint x = y / 2 + 1;
      /// @custom:key invariant 3 < y && 0 < z && 0 < x
      /// @custom:key invariant y / (z + 1) < z + 1 && y / (x + 1) < x + 1
      /// @custom:key invariant (z == y && x == y / 2 + 1) || x == (y / z + z) / 2
      /// @custom:key decreases z
      while (x < z) {
        z = x;
        x = (y / x + x) / 2;
      }
    } else if (y != 0) {
      z = 1;
    }
  }
}
local instance : InContract := ⟨Sqrt⟩
open scoped Scoped

/-- Unknown: of `sol_prove`'s four leaves, the `y <= 3` branch closes by
`sol_leaf; sol_close`; invariant initialization and the exit leaf stop
`sol_close_nonlin`'s bounded search or exhaust the heartbeats, preservation
likewise. Missing: a nonlinear division closer (`y / (x + 1) < x + 1` for the
Newton step, AM–GM over floor division; `(y / z + z) / 2 >= z → z * z <= y`). -/
def sqrtTarget := spec!{ sqrt }

end Solidity.Examples.Benchmark.MathLib.Sqrt
