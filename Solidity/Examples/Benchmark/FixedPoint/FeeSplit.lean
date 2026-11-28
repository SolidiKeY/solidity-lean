import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Fixed point: pro-rata payment splitting with rounding

Source: OpenZeppelin Contracts v4.9.6 `contracts/finance/PaymentSplitter.sol`,
`_pendingPayment`:
<https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v4.9.6/contracts/finance/PaymentSplitter.sol>.

`pendingPayment` is `_pendingPayment` as published, with `_shares[account]`
and `_totalShares` as parameters `shares`, `totalShares`. `splitTwo` is a
harness, not in the source: two payees with shares `s1`, `s2`
(`_totalShares = s1 + s2`), nothing released yet, as `release` would pay
each of them from `totalReceived`; it returns the sum of both payments.

Natural specifications: a payee is owed at most its pro-rata part, and the
rounded-down parts sum to at most the amount received.

Status (every clause kept exactly):
* `pendingPayment` unknown: leaf `(q + r) * T <= R * s` with
  `q = R * s / T - r`; `sol_close_nonlin` stops its bounded search; missing
  the quotient-of-product bound;
* `splitTwo` unknown: leaf `R * s1 / (s1 + s2) + R * s2 / (s1 + s2) <= R`;
  `sol_close` exhausts its heartbeats; missing the same bound and
  `a / d + b / d <= (a + b) / d`. Even `R * 0 / T == 0` stays open
  (symbolic divisor).
-/

namespace Solidity.Examples.Benchmark.FixedPoint.FeeSplit

/-- OpenZeppelin v4.9.6 `PaymentSplitter._pendingPayment`, and a two-payee harness. -/
def FeeSplit : Contract := contract!{
  ensures (\result + alreadyReleased) * totalShares <= totalReceived * shares;
  function pendingPayment(uint256 totalReceived, uint256 shares, uint256 totalShares, uint256 alreadyReleased)
      public pure returns (uint256) {
    return (totalReceived * shares) / totalShares - alreadyReleased;
  }
  ensures \result <= totalReceived;
  function splitTwo(uint256 totalReceived, uint256 s1, uint256 s2) public pure returns (uint256) {
    uint256 p1 = pendingPayment(totalReceived, s1, s1 + s2, 0);
    uint256 p2 = pendingPayment(totalReceived, s2, s1 + s2, 0);
    return p1 + p2;
  }
}
local instance : InContract := ⟨FeeSplit⟩
open scoped Scoped

/-- `_pendingPayment`: at most the pro-rata part. Unknown. -/
def pendingPayment_obligation : Fml FeeSplit [] := spec!{ pendingPayment }
/-- Two payees' rounded parts sum to at most the amount. Unknown. -/
def splitTwo_obligation : Fml FeeSplit [] := spec!{ splitTwo }



end Solidity.Examples.Benchmark.FixedPoint.FeeSplit
