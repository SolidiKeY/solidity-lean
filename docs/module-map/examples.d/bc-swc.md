| Module | Its examples |
|---|---|
| `Examples/Benchmark/Swc/IntegerOverflowMinimal.lean` | SWC-101 `integer_overflow_minimal.sol` (registry 1b62270), 0.4 wrapping `-=` as `unchecked`: `run` (`count == \old(count) - input`) refuted by a kernel-checked run from `count = 1` wrapping to 2^256-1. |
| `Examples/Benchmark/Swc/IntegerOverflowMinimalFixed.lean` | SWC-101 `integer_overflow_minimal_fixed.sol`, SafeMath `sub`: `run` proved under the same clause. |
| `Examples/Benchmark/Swc/WalletRefundNoSub.lean` | SWC-105 `wallet_02_refund_nosub.sol`: `refund` (`balances[msg.sender] == 0`) refuted by a run that pays and keeps the credit. Constructor, `withdraw`, `migrateTo` proved. `deposit` unknown (payable-snapshot leaf, as in WalletOk). |
| `Examples/Benchmark/Swc/WalletOk.lean` | SWC-105 `wallet_01_ok.sol`: constructor, `withdraw`, `refund`, `migrateTo` proved. `deposit` unknown: `old` is not resolved through the parallel payable update after the mapping save (closer gap, as in Defi/Escrow). |
| `Examples/Benchmark/Swc/MultiOwnedVulnerable.lean` | SWC-105 `multiowned_vulnerable.sol`, `onlyOwner` missing on `newOwner`: `newOwner` (only an owner adds owners) refuted by a run where a non-owner makes itself owner. Constructor and `deleteOwner` proved. |
| `Examples/Benchmark/Swc/MultiOwnedFixed.lean` | SWC-105 `multiowned_not_vulnerable.sol`: constructor, `newOwner`, `deleteOwner` proved under the same clauses. |
| `Examples/Benchmark/Swc/HashForEther.lean` | SWC-100 `visibility_not_set.sol`, default visibility written `public`: `_sendWinnings` (pays only a winner, `uint32(msg.sender) == 0`) refuted by a run paying account 1. `withdrawWinnings` proved. |
| `Examples/Benchmark/Swc/HashForEtherFixed.lean` | SWC-100 `visibility_not_set_fixed.sol`, `_sendWinnings` internal: `withdrawWinnings`, the only public function, proved. |
