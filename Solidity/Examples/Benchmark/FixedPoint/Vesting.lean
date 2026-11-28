import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Fixed point: linear vesting schedule

Source: OpenZeppelin Contracts v4.9.6 `contracts/finance/VestingWallet.sol`:
<https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v4.9.6/contracts/finance/VestingWallet.sol>.

The ether path's accounting kernel: `_vestingSchedule` as published, and
`release()` with `releasable()`/`vestedAmount()` inlined. `start()` and
`duration()` read the immutables `_start`, `_duration` (here storage
`uint256`s; the source's `uint64`s widen to `uint256` in `start()`). The
`uint64 timestamp` parameter and `uint64(block.timestamp)` in `releasable()`
are `uint256` here: no truncation (equal below `2^64`). The contract's ether balance
`address(this).balance` is the parameter `balance`; the
`Address.sendValue` payment and the event are omitted, so `release` only
updates `_released`.

Natural specifications: the vested amount never exceeds the allocation, and
`release` never makes `released` exceed the total ever received
(`balance + old released`) nor decrease it.

Status (every clause kept exactly):
* `vestingSchedule` unknown: the in-progress leaf
  `total * (t - start) / duration <= total` (under `t <= start + duration`)
  is not closed: `sol_close` exhausts its heartbeats; missing the bound
  `0 <= a → 0 <= b < d → a * b / d <= a`;
* `release` unknown: the same leaf, inlined, plus the snapshot save;
* proved: before `start` nothing is vested (`sol_prove`); from `end()` on
  everything is past `start + duration` (`sol_prove`, its leaf with the infeasible branch
  `t < start` by `sol_close`).
-/

namespace Solidity.Examples.Benchmark.FixedPoint.Vesting

/-- OpenZeppelin v4.9.6 `VestingWallet` ether accounting kernel. -/
def Vesting : Contract := contract!{
  uint256 released;
  uint256 start;
  uint256 duration;
  ensures \result <= totalAllocation;
  function vestingSchedule(uint256 totalAllocation, uint256 timestamp) public view returns (uint256) {
    if (timestamp < start) {
      return 0;
    } else if (timestamp > start + duration) {
      return totalAllocation;
    } else {
      return (totalAllocation * (timestamp - start)) / duration;
    }
  }
  ensures released <= balance + \old(released);
  ensures released >= \old(released);
  function release(uint256 balance) public {
    uint256 amount = vestingSchedule(balance + released, block.timestamp) - released;
    released += amount;
  }
}
local instance : InContract := ⟨Vesting⟩
open scoped Scoped

/-- `_vestingSchedule`: at most the allocation. Unknown (product/quotient bound). -/
def vestingSchedule_obligation : Fml Vesting [] := spec!{ vestingSchedule }
/-- `release`: released stays within the total received. Unknown (same bound). -/
def release_obligation : Fml Vesting [] := spec!{ release }

/-- Before `start`, nothing has vested. -/
theorem vestingSchedule_before :
    ⊢ dl!{ t < start → [ uint v = vestingSchedule(total, t); ] v == 0 } := by
  sol_prove


/-- Past `start + duration`, the whole allocation has vested. -/
theorem vestingSchedule_after :
    ⊢ dl!{ t > start + duration → [ uint v = vestingSchedule(total, t); ] v == total } := by
  sol_prove
  all_goals (sol_leaf; sol_close)

end Solidity.Examples.Benchmark.FixedPoint.Vesting
