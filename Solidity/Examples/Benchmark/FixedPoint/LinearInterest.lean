import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Fixed point: simple (linear) interest accrual

Source: Aave protocol v2 `contracts/protocol/libraries/math/MathUtils.sol`,
`calculateLinearInterest`:
<https://github.com/aave/protocol-v2/blob/ce53c4a8c8620125063168620eba0a8a92854eb8/contracts/protocol/libraries/math/MathUtils.sol>.

As published, public here: SafeMath's `sub`, `mul`, `add` are checked
`-`, `*`, `+` (same revert set), `SECONDS_PER_YEAR = 365 days` and
`WadRayMath.ray()` are the literals `31536000` and `1e27`, and the
`uint40` timestamp parameter is a `uint256` (its range is wider; every
`uint40` value is covered).

Natural specification: the accumulated index never falls below one ray, and
it is the published linear formula, truncation included. Proved.
-/

namespace Solidity.Examples.Benchmark.FixedPoint.LinearInterest

/-- Aave v2 `MathUtils.calculateLinearInterest`. -/
def LinearInterest : Contract := contract!{
  ensures \result >= 1000000000000000000000000000;
  ensures \result == rate * (block.timestamp - lastUpdateTimestamp) / 31536000 + 1000000000000000000000000000;
  function calculateLinearInterest(uint256 rate, uint256 lastUpdateTimestamp) public view returns (uint256) {
    uint256 timeDifference = block.timestamp - lastUpdateTimestamp;
    return (rate * timeDifference / 31536000) + 1000000000000000000000000000;
  }
}
local instance : InContract := ⟨LinearInterest⟩
open scoped Scoped

/-- At least one ray, and exactly `rate * Δt / year + ray`. -/
theorem calculateLinearInterest_spec : ⊢ spec!{ calculateLinearInterest } := by
  sol_prove

end Solidity.Examples.Benchmark.FixedPoint.LinearInterest
