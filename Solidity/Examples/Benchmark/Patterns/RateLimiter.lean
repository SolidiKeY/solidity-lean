import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Patterns benchmark: rate limiter per period

Source: ConsenSys Diligence, Smart Contract Best Practices, "Rate Limiting":
<https://github.com/ConsenSysDiligence/smart-contract-best-practices/blob/f3a9741ce3954a8dac3b3cbdcdafda14d8f4d948/docs/development-recommendations/precautions/rate-limiting.md>.

Changes: the fragment is wrapped in a contract; `block.number` is
`block.timestamp` (this model has no block number, so a period is measured
in seconds, not blocks; under 0.8 checked arithmetic the addition reverts on
overflow, so the source's `require(totalAmount >= …)` can no longer fail); the pre-0.7 `constructor(…) public` drops
`public`, the messages take double quotes,
`updatePeriod` is declared before its caller (this model inlines a call to an
earlier function) and `msg.sender.transfer` is `payable(msg.sender).transfer`.
Natural `@custom:key` clauses: after a withdrawal the period's total stays
below the limit, the period rolls over when it has ended, and the caller is paid.

Verdicts: constructor proved; withdraw unknown. `updatePeriod` is internal
and inlined, with no clause of its own.
-/
namespace Solidity.Examples.Benchmark.Patterns.RateLimiter
def RateLimiter : Contract := contract!{
  uint internal period;
  uint internal limit;
  uint internal currentPeriodEnd;
  uint internal currentPeriodAmount;
  ensures period == _period && limit == _limit && currentPeriodEnd == block.timestamp + _period;
  constructor(uint _period, uint _limit) {
    period = _period;
    limit = _limit;
    currentPeriodEnd = block.timestamp + period;
  }
  function updatePeriod() internal {
    if (currentPeriodEnd < block.timestamp) {
      currentPeriodEnd = block.timestamp + period;
      currentPeriodAmount = 0;
    }
  }
  ensures currentPeriodAmount < limit && period == \old(period) && limit == \old(limit);
  ensures \old(currentPeriodEnd) < block.timestamp -> currentPeriodAmount == amount && currentPeriodEnd == block.timestamp + period;
  ensures \old(currentPeriodEnd) >= block.timestamp -> currentPeriodAmount == \old(currentPeriodAmount) + amount && currentPeriodEnd == \old(currentPeriodEnd);
  ensures msg.sender != this -> net(msg.sender) == \old(net(msg.sender)) - amount;
  function withdraw(uint amount) public {
    updatePeriod();
    uint totalAmount = currentPeriodAmount + amount;
    require(totalAmount >= currentPeriodAmount, "overflow");
    require(currentPeriodAmount + amount < limit, "exceeds period limit");
    currentPeriodAmount += amount;
    payable(msg.sender).transfer(amount);
  }
}
local instance : InContract := ⟨RateLimiter⟩
open scoped Scoped
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove
/-- Unknown: `sol_prove` and `sol_auto` leave both period branches. On the
rollover branch the leaf holds three saves to the period slots, the payment
and the snapshot; closing it needs read-over-repeated-save normalization of
`currentPeriodAmount` with the ledger debit. The full obligation is retained. -/
def withdraw_obligation : Fml RateLimiter [] := spec!{ withdraw }
end Solidity.Examples.Benchmark.Patterns.RateLimiter
