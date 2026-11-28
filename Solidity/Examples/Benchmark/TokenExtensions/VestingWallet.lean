import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Vesting wallet release (OpenZeppelin 5.0.2 `VestingWallet`, ether)

Sources (OpenZeppelin 5.0.2):
<https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/dbb6104ce834628e473d2173bbc9d47f81a9eec3/contracts/finance/VestingWallet.sol>
and the same commit's `contracts/utils/Address.sol` (`sendValue`).

The ether path: `start`, `duration`, `end` (spelt `end_`, a Lean keyword), `released`, `releasable`,
`vestedAmount`, `_vestingSchedule`, `release`. Changes: `uint64` timestamps
and the `uint64(block.timestamp)` cast are `uint` words; `Ownable` is a stored
`_owner` (its transfer functions omitted); `Address.sendValue` is inlined as
its balance check, `call{value: amount}("")` and success check; the ERC-20
overloads, events and inheritance are omitted.

Natural spec: the schedule releases nothing before `start` and at most the
total allocation; `release()` raises `released()` by exactly the releasable
amount it computed, and pays only after booking it.

Verdicts: constructor, end proved; _vestingSchedule UNKNOWN (ternary and
nonlinear bound), its before-start clause proved; release UNKNOWN at the
payment update.
-/
namespace Solidity.Examples.Benchmark.TokenExtensions.VestingWallet

def VestingWallet : Contract := contract!{
  uint _released;
  address _owner;
  uint immutable _start;
  uint immutable _duration;
  ensures _owner == beneficiary && _start == startTimestamp && _duration == durationSeconds;
  constructor(address beneficiary, uint startTimestamp, uint durationSeconds) {
    _owner = beneficiary;
    _start = startTimestamp;
    _duration = durationSeconds;
  }
  ensures \result == _start + _duration;
  function end_() returns (uint) {
    return _start + _duration;
  }
  ensures timestamp < _start -> \result == 0;
  ensures timestamp >= _start + _duration -> \result == totalAllocation;
  ensures \result <= totalAllocation;
  function _vestingSchedule(uint totalAllocation, uint timestamp) returns (uint) {
    if (timestamp < _start) {
      return 0;
    } else {
      uint e = end_();
      if (timestamp >= e) {
        return totalAllocation;
      } else {
        return (totalAllocation * (timestamp - _start)) / _duration;
      }
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
theorem constructor_obligation : ⊢ spec!{ constructor } := by
  sol_prove
/-- PROVED: `end()` is `start + duration`. -/
theorem end_obligation : ⊢ spec!{ end_ } := by
  sol_prove
/-- UNKNOWN: the inlined returns leave a ternary binding
`se3 := (se10 ? se1 : se1 * (se2 - find(storage, _start)) / find(storage, _duration))`
and the bound `result <= totalAllocation` needs the nonlinear fact
`a * (t - s) / d <= a` for `t - s < d`; even the `timestamp < _start` leaf of the
whole clause list stays open (its first clause alone is `vestingSchedule_beforeStart`). -/
def vestingSchedule_obligation := spec!{ _vestingSchedule }
/-- UNKNOWN: every leaf ends in the payment update `{ pay(owner, amount) ‖ success := true }`,
through which no read of `_released` or `address(this).balance` closes. -/
def release_obligation := spec!{ release }
/-- PROVED component: nothing is vested before `start`. -/
theorem vestingSchedule_beforeStart : ⊢ dl!{
    timestamp < _start → [ uint r = _vestingSchedule(total, timestamp); ] r == 0 } := by
  sol_prove
/-- UNKNOWN component: nothing is released before `start`, at the `pay` update. -/
def release_beforeStart : Fml VestingWallet [] := dl!{
    r0 == _released && block.timestamp < _start → [ release(); ] _released == r0 }
/-- UNKNOWN component: `released()` never decreases, at the `pay` update. -/
def release_monotone : Fml VestingWallet [] := dl!{ r0 == _released → [ release(); ] _released >= r0 }

end Solidity.Examples.Benchmark.TokenExtensions.VestingWallet
