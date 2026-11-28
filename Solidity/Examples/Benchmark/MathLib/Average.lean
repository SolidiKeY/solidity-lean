import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: overflow-free average

Source: OpenZeppelin Contracts v4.9.6, `Math.average`,
<https://github.com/OpenZeppelin/openzeppelin-contracts/blob/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/utils/math/Math.sol#L30-L37>.

Changes: `public` instead of `internal` (a call inlines either way) and the
`@custom:key` clauses. The body is the source's.

Natural specification: the result is `⌊(a + b) / 2⌋` over the integers. A
clause's arithmetic is Solidity's, checked at `uint256`
(`Calculus/SurfaceSpec.lean`), so `(a + b) / 2` would be false where
`a + b` overflows. The first clause is the familiar form where the sum fits,
the second the same quantity for every input, written without overflow.
-/
namespace Solidity.Examples.Benchmark.MathLib.Average

def Average : Contract := contract!{
  ensures a <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 - b -> \result == (a + b) / 2;
  ensures \result == a / 2 + b / 2 + (a % 2) * (b % 2);
  function average(uint256 a, uint256 b) public pure returns (uint256) {
    return (a & b) + (a ^ b) / 2;
  }
}
local instance : InContract := ⟨Average⟩
open scoped Scoped

/-- Unknown: the single leaf needs `(a & b) + (a ^ b) / 2 = ⌊(a + b) / 2⌋`
over `Semantics.uintBitwise`. `sol_prove` leaves it, and
`sol_leaf; sol_close` exhausts its heartbeats. Missing: a closer fact for
the carry identity `a + b = 2 * (a & b) + (a ^ b)` on words. -/
def averageTarget := spec!{ average }

end Solidity.Examples.Benchmark.MathLib.Average
