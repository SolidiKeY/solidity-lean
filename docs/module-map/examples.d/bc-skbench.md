| Module | Its examples |
|---|---|
| `Examples/Benchmark/SolkeyBench/AccessRestriction.lean` | solkey 50a1469 `benchmark/AccessRestriction.sol`, modifiers inlined: `changeOwner` proved. `disown` unknown: owner = 0 after `delAt` (delete) not closed. `forceOwnerChange` unknown: `x & 0 == 1` branch not refuted (bitwise-and closer missing) and refund needs the pay ledger rule. |
| `Examples/Benchmark/SolkeyBench/Fund.lean` | solkey 50a1469 `benchmark/Fund.sol`: `withdraw` unknown: cleared share, oldNet debit and mapping frame after save/pay; mapping-frame closure and pay ledger rule missing. |
| `Examples/Benchmark/SolkeyBench/SendContract.lean` | solkey 50a1469 `benchmark/SendContract.sol`: constructor proved. `becomeRichest` unknown: net debit of the old richest after `pay`; pay ledger rule missing. |
| `Examples/Benchmark/SolkeyBench/SendingEther.lean` | solkey 50a1469 `benchmark/SendingEther.sol` (`SendEther` only): `sendViaTransfer`, `sendViaSend`, `sendViaCall` unknown: net clauses after `pay(_to, msg.value)`; pay ledger rule missing. |
| `Examples/Benchmark/SolkeyBench/SimpleAuction.lean` | solkey 50a1469 `benchmark/SimpleAuction.sol` (solkey variant; distinct from Governance/EnglishAuction): constructor proved. `bid`, `withdraw` unknown: mapping/snapshot closure (and pay for withdraw). `auctionEnd` unknown: pay ledger rule missing. |
| `Examples/Benchmark/SolkeyBench/Todos.lean` | solkey 50a1469 `benchmark/Todos.sol`: `toggleCompleted` proved (struct array field toggle, length frame). `get`, `updateText` carry no clauses. |
| `Examples/Benchmark/SolkeyBench/WithdrawalContract.lean` | solkey 50a1469 `benchmark/WithdrawalContract.sol`: constructor proved. `becomeRichest` unknown: credit to old richest and mapping frame; `withdraw` unknown: as Fund. |
