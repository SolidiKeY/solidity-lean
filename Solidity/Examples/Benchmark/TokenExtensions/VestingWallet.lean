import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Vesting wallet release (OpenZeppelin 5.0.2 `VestingWallet`, ether)

Sources (OpenZeppelin 5.0.2): <https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/dbb6104ce834628e473d2173bbc9d47f81a9eec3/contracts/finance/VestingWallet.sol> and the same
commit's `utils/Address.sol` (`sendValue`). The ether path; `uint64` timestamps
and casts are `uint`; `Ownable` is a stored nonzero `_owner`; `end` is `end_` (a Lean
keyword); `sendValue` is inlined as its balance check, call and success check;
the ERC-20 overloads, events and inheritance are omitted.
Natural spec: nothing vests before `start`, everything after `end`, never more
than the allocation; `release()` never lowers `released()`, releases nothing
before `start` and, under the no-callback payment model, empties the wallet
after `end`.
Verdicts: on each declaration below.
-/
namespace Solidity.Examples.Benchmark.TokenExtensions.VestingWallet
def VestingWallet : Contract := contract!{
  uint _released;
  address _owner;
  uint immutable _start;
  uint immutable _duration;
  ensures _owner == beneficiary && beneficiary != address(0) && _start == startTimestamp && _duration == durationSeconds;
  constructor(address beneficiary, uint startTimestamp, uint durationSeconds) {
    if (beneficiary == address(0)) { revert(); }
    _owner = beneficiary;
    _start = startTimestamp;
    _duration = durationSeconds;
  }
  ensures \result == _start + _duration;
  function end_() returns (uint) { return _start + _duration; }
  ensures timestamp < _start -> \result == 0;
  ensures timestamp >= _start + _duration -> \result == totalAllocation;
  ensures \result <= totalAllocation;
  function _vestingSchedule(uint totalAllocation, uint timestamp) returns (uint) {
    if (timestamp < _start) { return 0; } else {
      uint e = end_();
      if (timestamp >= e) { return totalAllocation; } else { return (totalAllocation * (timestamp - _start)) / _duration; }
    }
  }
  ensures block.timestamp < _start -> _released == \old(_released);
  ensures _released >= \old(_released);
  ensures block.timestamp >= _start + _duration && _owner != address(this) -> address(this).balance == 0;
  function release() {
    uint total = address(this).balance + _released;
    uint vested = _vestingSchedule(total, block.timestamp);
    uint amount = vested - _released;
    _released += amount;
    require(address(this).balance >= amount);
    (bool success, ) = _owner.call{value: amount}("");
    require(success);
  }
}
local instance : InContract := ⟨VestingWallet⟩
open scoped Scoped
/-- PROVED: owner, start and duration stored. -/
theorem constructor_obligation : ⊢ spec!{ constructor } := by sol_prove
/-- PROVED: `end()` is `start + duration`. -/
theorem end_obligation : ⊢ spec!{ end_ } := by sol_prove
/-- UNKNOWN: a ternary binding from the inlined returns, and the nonlinear bound
`a * (t - s) / d <= a`; its first clause is `vestingSchedule_beforeStart`. -/
def vestingSchedule_obligation := spec!{ _vestingSchedule }
/-- UNKNOWN: no read of `_released` or the balance closes through the leaf's
payment update `{ pay(owner, amount) ‖ success := true }`. -/
def release_obligation := spec!{ release }
/-- PROVED component: nothing is vested before `start`. -/
theorem vestingSchedule_beforeStart : ⊢ dl!{
    timestamp < _start → [ uint r = _vestingSchedule(total, timestamp); ] r == 0 } := by sol_prove

end Solidity.Examples.Benchmark.TokenExtensions.VestingWallet
