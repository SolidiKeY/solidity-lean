import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Fixed point: linear bonding curve buy/sell round trip

Source: Ratimon/bonding-curves `src/pricings/LinearCurve.sol` (`getPoolBalance`)
and `src/examples/LinearBondingCurve.sol` (`calculatePurchaseAmountOut`):
<https://github.com/Ratimon/bonding-curves/blob/1518a8d5f389ecc506095f01d9e718962858f65a/src/pricings/LinearCurve.sol>,
<https://github.com/Ratimon/bonding-curves/blob/1518a8d5f389ecc506095f01d9e718962858f65a/src/examples/LinearBondingCurve.sol>.

Price `slope * supply + initialPrice`; its integral, the pool balance, is
`getPoolBalance(s) = slope.mul(powu(s, 2)).div(2e18).add(s.mul(initialPrice))`
in PRB-math `UD60x18`, spelled here in `uint256` as PRB defines the
operations: `a.mul(b) = a * b / 1e18`, `a.div(b) = a * 1e18 / b`,
`powu(s, 2) = s.mul(s)` (all truncating). PRB computes these with a
512-bit intermediate (`mulDiv18`, `mulDiv`) and reverts only when the
result overflows; here the intermediate product is checked, so the model
reverts on more inputs and returns the same value wherever it does not. `buy` charges
`getPoolBalance(totalPurchased + amount) - getPoolBalance(totalPurchased)`,
the source's `calculatePurchaseAmountOut`, and records supply and reserve.
The source sells only (no redemption); `sell` is its mirror, added for the
round trip: it refunds `getPoolBalance(totalPurchased) -
getPoolBalance(totalPurchased - amount)`. Token transfers, the sale cap and
duration of the source's `BondingCurve` are omitted.

Status:
* `buy`, `sell` proved: supply and reserve move by the amount and the price;
* round trip (buy then sell the same amount restores supply and reserve and
  refunds exactly the cost) unknown: `sol_prove` leaves the leaf with two
  syntactically equal `getPoolBalance` chains bound under different fresh
  names, and `sol_close` hits `simp`'s recursion limit; missing a closer
  step identifying equal update chains (common-subterm sharing) before
  `simp`. The statement is kept as `roundTrip_obligation`.
-/

namespace Solidity.Examples.Benchmark.FixedPoint.BondingCurve

/-- Ratimon `LinearCurve` pricing, buying and its mirror sale. -/
def BondingCurve : Contract := contract!{
  uint256 slope;
  uint256 initialPrice;
  uint256 totalPurchased;
  uint256 reserve;
  function getPoolBalance(uint256 tokenSupply) public view returns (uint256) {
    return slope * (tokenSupply * tokenSupply / 1000000000000000000) / 1000000000000000000
        * 1000000000000000000 / 2000000000000000000 + tokenSupply * initialPrice / 1000000000000000000;
  }
  ensures totalPurchased == \old(totalPurchased) + amount;
  ensures reserve == \old(reserve) + \result;
  function buy(uint256 amount) public returns (uint256) {
    uint256 cost = getPoolBalance(totalPurchased + amount) - getPoolBalance(totalPurchased);
    totalPurchased += amount;
    reserve += cost;
    return cost;
  }
  ensures totalPurchased == \old(totalPurchased) - amount;
  ensures reserve == \old(reserve) - \result;
  function sell(uint256 amount) public returns (uint256) {
    uint256 refund = getPoolBalance(totalPurchased) - getPoolBalance(totalPurchased - amount);
    totalPurchased -= amount;
    reserve -= refund;
    return refund;
  }
}
local instance : InContract := ⟨BondingCurve⟩
open scoped Scoped

/-- `buy`: supply up by the amount, reserve up by the cost. -/
theorem buy_spec : ⊢ spec!{ buy } := by
  sol_prove
/-- `sell`: supply down by the amount, reserve down by the refund. -/
theorem sell_spec : ⊢ spec!{ sell } := by
  sol_prove
/-- Buy then sell the same amount: supply and reserve restored, refund = cost.
Unknown (see the module docstring). -/
def roundTrip_obligation : Fml BondingCurve [] := dl!{ [ uint s0 = totalPurchased; uint r0 = reserve; uint a = buy(n);
    uint b = sell(n); uint s1 = totalPurchased; uint r1 = reserve; ]
    (s1 == s0 ∧ r1 == r0 ∧ a == b) }

end Solidity.Examples.Benchmark.FixedPoint.BondingCurve
