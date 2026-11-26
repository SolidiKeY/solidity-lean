import Solidity.Frontend.Testing
import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Closers

/-!
# DeFi: complete staking rewards pool

Source: <https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/defi/staking-rewards/StakingRewards.sol>.
`StakingPool.sol` retains the entire original program and IERC20 interface;
only `@custom:key` specifications are added. H1710 authorizes the existing
solc importer instead of native `contract!` for this module. The adjacent AST
pins the compiler, source digest and analysis settings; it is not an EVM
execution or compiler-equivalence proof. The importer admits nine explicit functions. The full funding function is
retained but currently unknown at its nested balanceOf call; the admission pin
below records the exact refusal. Transfer return values remain ignored,
as in the source, so no unconditional foreign-token delivery is promised.
The separate StakingRewards module retains the proved reward equations.
-/
solc_import "StakingPool.ast.json" hash 0xf8e2ef2edc17d9a7
  as Solidity.Examples.Benchmark.Defi.StakingPool.StakingRewards testing

namespace Solidity.Examples.Benchmark.Defi.StakingPool
local instance : InContract := ⟨StakingRewards⟩
open scoped Scoped

#guard StakingRewards.report.length == 10
#guard StakingRewards.report.all fun r => match r.status with
  | .elaborated => r.name != "notifyRewardAmount"
  | .unsupported => r.name == "notifyRewardAmount" &&
      r.reason == "StakingPool.sol:133: rewardsToken.balanceOf(…): the callee is not a function value"
  | _ => false

set_option Elab.async false

/-- Exact source specification of `constructor`; isolated proof attempt recorded separately. -/
def constructor_obligation : Fml StakingRewards [] := spec!{ constructor }
/-- Exact source specification of `lastTimeRewardApplicable`; isolated proof attempt recorded separately. -/
def lastTimeRewardApplicable_obligation : Fml StakingRewards [] := spec!{ lastTimeRewardApplicable }
/-- Exact source specification of `rewardPerToken`; isolated proof attempt recorded separately. -/
def rewardPerToken_obligation : Fml StakingRewards [] := spec!{ rewardPerToken }
/-- Exact source specification of `stake`; isolated proof attempt recorded separately. -/
def stake_obligation : Fml StakingRewards [] := spec!{ stake }
/-- Exact source specification of `withdraw`; isolated proof attempt recorded separately. -/
def withdraw_obligation : Fml StakingRewards [] := spec!{ withdraw }
/-- Exact source specification of `earned`; isolated proof attempt recorded separately. -/
def earned_obligation : Fml StakingRewards [] := spec!{ earned }
/-- Exact source specification of `getReward`; isolated proof attempt recorded separately. -/
def getReward_obligation : Fml StakingRewards [] := spec!{ getReward }
/-- Exact source specification of `setRewardsDuration`; isolated proof attempt recorded separately. -/
def setRewardsDuration_obligation : Fml StakingRewards [] := spec!{ setRewardsDuration }
/-- Exact source specification of `_min`; isolated proof attempt recorded separately. -/
def _min_obligation : Fml StakingRewards [] := spec!{ _min }

end Solidity.Examples.Benchmark.Defi.StakingPool
