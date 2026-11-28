import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Fixed point: RAY mul/div rounded half up

Source: Aave protocol v2 `contracts/protocol/libraries/math/WadRayMath.sol`:
<https://github.com/aave/protocol-v2/blob/ce53c4a8c8620125063168620eba0a8a92854eb8/contracts/protocol/libraries/math/WadRayMath.sol>.

`rayMul` and `rayDiv` as published, public here; `RAY = 1e27` and
`halfRAY = RAY / 2` are inlined literals, `Errors.MATH_MULTIPLICATION_OVERFLOW`
(`"48"`) and `Errors.MATH_DIVISION_BY_ZERO` (`"50"`) their string values,
which a `require` drops. The WAD variants differ only in the constant.

Natural specifications state rounding to nearest, ties up: `q` rounds
`n / d` half up iff `q * d <= n + d / 2 < (q + 1) * d`, the upper bound
written `n + d / 2 - q * d < d`, which cannot overflow where the body
returns (clause arithmetic is checked at `uint256`; `(q + 1) * d` overflows
at `rayMul(max - 5e26, 1)`).

The source is `pragma solidity 0.6.12`, unchecked; here arithmetic is
checked (0.8). The `require` guards exclude every overflow, so the two
agree.

Status (every clause kept exactly):
* `rayMul`, `rayDiv` unknown: the leaves `q = (a * b + halfRAY) / RAY ⟹ …`
  (and the `a == 0 || b == 0` branch) exhaust `sol_close`'s heartbeats in
  `simp`; missing the same quotient-of-product bound as `WadMath`;
* proved: `rayMul(0, b) == 0`.
-/

namespace Solidity.Examples.Benchmark.FixedPoint.RayMath

/-- Aave v2 `WadRayMath.rayMul`/`rayDiv`, with half-up rounding clauses. -/
def RayMath : Contract := contract!{
  ensures \result * 1000000000000000000000000000 <= a * b + 500000000000000000000000000;
  ensures a * b + 500000000000000000000000000 - \result * 1000000000000000000000000000 < 1000000000000000000000000000;
  function rayMul(uint256 a, uint256 b) public pure returns (uint256) {
    if (a == 0 || b == 0) {
      return 0;
    }
    require(a <= (type(uint256).max - 500000000000000000000000000) / b, "48");
    return (a * b + 500000000000000000000000000) / 1000000000000000000000000000;
  }
  ensures \result * b <= a * 1000000000000000000000000000 + b / 2;
  ensures a * 1000000000000000000000000000 + b / 2 - \result * b < b;
  function rayDiv(uint256 a, uint256 b) public pure returns (uint256) {
    require(b != 0, "50");
    uint256 halfB = b / 2;
    require(a <= (type(uint256).max - halfB) / 1000000000000000000000000000, "48");
    return (a * 1000000000000000000000000000 + halfB) / b;
  }
}
local instance : InContract := ⟨RayMath⟩
open scoped Scoped

/-- `rayMul`: half-up rounding. Unknown (closer heartbeats in `simp`). -/
def rayMul_obligation : Fml RayMath [] := spec!{ rayMul }
/-- `rayDiv`: half-up rounding. Unknown (closer heartbeats in `simp`). -/
def rayDiv_obligation : Fml RayMath [] := spec!{ rayDiv }

/-- `rayMul(0, b)` takes the early return: `0`. -/
theorem rayMul_zero : ⊢ dl!{ [ uint z = rayMul(0, b); ] z == 0 } := by
  sol_prove

end Solidity.Examples.Benchmark.FixedPoint.RayMath
