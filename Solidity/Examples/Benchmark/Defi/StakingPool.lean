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
Verdicts: constructor and setRewardsDuration proved below. All other admitted
functions are unknown: _min and lastTimeRewardApplicable leave symbolic
conditional/alias branches; rewardPerToken and earned additionally leave
nonlinear division equations; stake, withdraw and getReward leave mapping,
old-state accrual and foreign-call frame goals. Missing closures are conditional
normalization, nonlinear reward arithmetic and snapshot/mapping frames.
notifyRewardAmount is unknown at admission, as pinned below.
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

/-- Exact source specification of `constructor`; proved below. -/
def constructor_obligation : Fml StakingRewards [] := spec!{ constructor }
/-- Exact source specification of `lastTimeRewardApplicable`; unknown: exact obligation retained; see module verdicts. -/
def lastTimeRewardApplicable_obligation : Fml StakingRewards [] := spec!{ lastTimeRewardApplicable }
/-- Exact source specification of `rewardPerToken`; unknown: exact obligation retained; see module verdicts. -/
def rewardPerToken_obligation : Fml StakingRewards [] := spec!{ rewardPerToken }
/-- Exact source specification of `stake`; unknown: exact obligation retained; see module verdicts. -/
def stake_obligation : Fml StakingRewards [] := spec!{ stake }
/-- Exact source specification of `withdraw`; unknown: exact obligation retained; see module verdicts. -/
def withdraw_obligation : Fml StakingRewards [] := spec!{ withdraw }
/-- Exact source specification of `earned`; unknown: exact obligation retained; see module verdicts. -/
def earned_obligation : Fml StakingRewards [] := spec!{ earned }
/-- Exact source specification of `getReward`; unknown: exact obligation retained; see module verdicts. -/
def getReward_obligation : Fml StakingRewards [] := spec!{ getReward }
/-- Exact source specification of `setRewardsDuration`; proved below. -/
def setRewardsDuration_obligation : Fml StakingRewards [] := spec!{ setRewardsDuration }
/-- Exact source specification of `_min`; unknown: exact obligation retained; see module verdicts. -/
def _min_obligation : Fml StakingRewards [] := spec!{ _min }

/-- Solidity constructor: owner/token bindings and zero-initialized accounting. -/
theorem constructor_spec : ⊢ spec!{ constructor } := by sol_prove
/-- Solidity setRewardsDuration: requested duration with owner, finish and rate framed. -/
theorem setRewardsDuration_spec : ⊢ spec!{ setRewardsDuration } := by sol_prove

end Solidity.Examples.Benchmark.Defi.StakingPool
