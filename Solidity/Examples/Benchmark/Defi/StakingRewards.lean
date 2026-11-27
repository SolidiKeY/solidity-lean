import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# DeFi: staking reward-per-token calculator

Source: Synthetix StakingRewards, Solidity by Example snapshot:
<https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/defi/staking-rewards/StakingRewards.sol>.

This standalone calculator extracts the source's two reward equations. Its
arguments are the source's balances, stored accumulator, elapsed eligible time,
reward rate and prior reward-per-token snapshot. Passing elapsed eligible time
rather than reading the clock isolates these equations from timestamp/funding
policy. It does not implement a staking pool, token transfers or notification.
The 1e18 scale, zero-supply branch, multiplication/division order and truncation
are retained. In particular, division precedes adding stored rewards.

Specifications state the complete returned equations, including zero supply.
Checked overflow and a paid snapshot above the accumulator revert; the box
specifications do not assert totality on these inputs.
-/
namespace Solidity.Examples.Benchmark.Defi.StakingRewards

def StakingRewards : Contract := contract!{
  ensures supply == 0 -> \result == stored;
  ensures supply != 0 -> \result == stored + elapsed * rate * 1000000000000000000 / supply;
  function rewardPerToken(uint supply, uint stored, uint elapsed, uint rate)
      public pure returns (uint) {
    if (supply == 0) { return stored; }
    return stored + elapsed * rate * 1000000000000000000 / supply;
  }
  ensures \result == balance * (accumulator - paid) / 1000000000000000000 + stored;
  function earned(uint balance, uint accumulator, uint paid, uint stored)
      public pure returns (uint) {
    return balance * (accumulator - paid) / 1000000000000000000 + stored;
  }
}
local instance : InContract := ⟨StakingRewards⟩
open scoped Scoped

/-- Empty pools do not accrue per-token rewards; nonempty pools accrue pro rata. -/
theorem rewardPerToken_spec : ⊢ spec!{ rewardPerToken } := by sol_prove
/-- Earned rewards retain stored credit and add the truncated accumulator delta. -/
theorem earned_spec : ⊢ spec!{ earned } := by sol_prove

end Solidity.Examples.Benchmark.Defi.StakingRewards
