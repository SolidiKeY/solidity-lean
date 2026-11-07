| `Yul/World/LifecycleBalancesFit.lean` | BalancesFit through the EIP-6780 self-beneficiary burn, destruct transfer and finalization. |
| `Yul/Views/SourceBalanceExact.lean` | The actual evaluator's `BALANCE` of an instance returns its exact Nat balance under BalancesFit; a `2 ^ 256` balance is observed as `0` without it. |
