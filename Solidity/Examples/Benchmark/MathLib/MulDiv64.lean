import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `mulDiv` for `uint64` operands

Source: OpenZeppelin Contracts v4.9.6, `Math.mulDiv`,
<https://github.com/OpenZeppelin/openzeppelin-contracts/blob/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/utils/math/Math.sol#L50-L55>: "floor(x * y / denominator) with
full precision. Throws if result overflows a uint256 or denominator == 0".

Changes: the source's 512-bit Remco Bloemen algorithm exists for 256-bit
operands. For `uint64` operands the product fits in `uint256`, so the full
precision computation is the plain one, at the operands' width: the result
reverts where it overflows its type, as the source's does
(`require(denominator > prod1)`), and dividing by zero panics.

Natural specification: `result = ⌊x * y / denominator⌋`. The obligation
ranges the `uint64` parameters over `uint256` (the elaborator reads a
narrow parameter as a `uint`), a larger domain than the source's.
-/
namespace Solidity.Examples.Benchmark.MathLib.MulDiv64

def MulDiv64 : Contract := contract!{
  ensures \result == x * y / denominator;
  function mulDiv(uint64 x, uint64 y, uint64 denominator) public pure returns (uint64) {
    uint256 r = uint256(x) * uint256(y) / uint256(denominator);
    require(r <= type(uint64).max);
    return uint64(r);
  }
}
local instance : InContract := ⟨MulDiv64⟩
open scoped Scoped

/-- `mulDiv`: the floor of the exact quotient, wherever it returns. -/
theorem spec_mulDiv : ⊢ spec!{ mulDiv } := by sol_prove <;> (sol_leaf; sol_close)

end Solidity.Examples.Benchmark.MathLib.MulDiv64
