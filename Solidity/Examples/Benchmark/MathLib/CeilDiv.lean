import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: ceiling division

Source: OpenZeppelin Contracts v4.9.6, `Math.ceilDiv`,
<https://github.com/OpenZeppelin/openzeppelin-contracts/blob/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/utils/math/Math.sol#L39-L48>.

Changes: `public` instead of `internal` and the `@custom:key` clauses. The
body is the source's: `(a + b - 1) / b` could overflow, so it distributes.

Natural specification: `⌈a / b⌉`, i.e. `0` for `a = 0` and otherwise
`a / b` rounded up by the remainder. A positive `a` with `b = 0` divides by
zero and panics, which every box formula admits; `ceilDiv(0, 0)` is `0`, as
in the source.
-/
namespace Solidity.Examples.Benchmark.MathLib.CeilDiv

def CeilDiv : Contract := contract!{
  ensures a == 0 -> \result == 0;
  ensures a > 0 && a % b == 0 -> \result == a / b;
  ensures a > 0 && a % b != 0 -> \result == a / b + 1;
  function ceilDiv(uint256 a, uint256 b) public pure returns (uint256) {
    return a == 0 ? 0 : (a - 1) / b + 1;
  }
}
local instance : InContract := ⟨CeilDiv⟩
open scoped Scoped

/-- Unknown: the leaf needs `(a - 1) / b + 1` against `a / b` and `a % b`
for a symbolic divisor `b` (`a - 1 = q * b + r` case analysis).
`sol_prove` leaves it and `sol_leaf; sol_close` exhausts its heartbeats.
Missing: a division/remainder closer relating `(a - 1) / b` to `a / b`
and `a % b` for variable `b`. -/
def ceilDivTarget := spec!{ ceilDiv }

end Solidity.Examples.Benchmark.MathLib.CeilDiv
