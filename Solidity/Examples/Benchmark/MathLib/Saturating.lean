import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: saturating addition and subtraction

Source: OpenZeppelin Contracts v5.4.0, `Math.saturatingAdd` and
`Math.saturatingSub` <https://github.com/OpenZeppelin/openzeppelin-contracts/blob/c64a1edb67b6e3f4a15cca8909c9482ad33a02b0/contracts/utils/math/Math.sol#L112-L126>,
with `tryAdd`, `trySub` <https://github.com/OpenZeppelin/openzeppelin-contracts/blob/c64a1edb67b6e3f4a15cca8909c9482ad33a02b0/contracts/utils/math/Math.sol#L48-L68>
and `ternary` <https://github.com/OpenZeppelin/openzeppelin-contracts/blob/c64a1edb67b6e3f4a15cca8909c9482ad33a02b0/contracts/utils/math/Math.sol#L136-L150>.

Changes: `public` instead of `internal`, the `@custom:key` clauses, and
the helpers inlined (tuple returns are not modelled): `SafeCast.toUint(b)`
(assembly `iszero(iszero(b))`) is `b ? 1 : 0`, and `(bool success, uint256
result) = tryAdd(a, b)` binds the helper's two locals. The branchless
arithmetic is the source's.

Natural specification: `a + b` capped at `2^256 - 1`; `a - b` floored at `0`.
-/
namespace Solidity.Examples.Benchmark.MathLib.Saturating

def Saturating : Contract := contract!{
  ensures a <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 - b -> \result == a + b;
  ensures a > 115792089237316195423570985008687907853269984665640564039457584007913129639935 - b -> \result == 115792089237316195423570985008687907853269984665640564039457584007913129639935;
  function saturatingAdd(uint256 a, uint256 b) public pure returns (uint256) {
    unchecked {
      uint256 c = a + b;
      bool success = c >= a;
      uint256 result = c * (success ? 1 : 0);
      return type(uint256).max ^ ((result ^ type(uint256).max) * (success ? 1 : 0));
    }
  }
  ensures a >= b -> \result == a - b;
  ensures a < b -> \result == 0;
  function saturatingSub(uint256 a, uint256 b) public pure returns (uint256) {
    unchecked {
      uint256 c = a - b;
      bool success = c <= a;
      return c * (success ? 1 : 0);
    }
  }
}
local instance : InContract := ⟨Saturating⟩
open scoped Scoped

/-- `saturatingSub`: the difference, or `0` below it. -/
theorem spec_saturatingSub : ⊢ spec!{ saturatingSub } := by
  sol_prove <;> (sol_leaf; sol_close)

/-- Unknown: the leaf needs the branchless select `m ^ ((r ^ m) * s)`
(`s ∈ {0, 1}`) to be `r` or `m`, and the wrap `c < a` to mean overflow;
`sol_leaf; sol_close` exhausts its heartbeats. Missing: a closer for
`xor` against itself (`m ^ (r ^ m) = r`, `m ^ 0 = m`) over
`Semantics.uintBitwise`. -/
def saturatingAddTarget := spec!{ saturatingAdd }

end Solidity.Examples.Benchmark.MathLib.Saturating
