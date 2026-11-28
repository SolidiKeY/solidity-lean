| Module | Its examples |
|---|---|
| `Examples/Benchmark/SolkeyMisc/Account.lean` | solkey real-world `Account` (solidity-by-example error handling): `deposit` and `withdraw` proved by `sol_prove`. |
| `Examples/Benchmark/SolkeyMisc/DocsBallot.lean` | solkey real-world `DocsBallot` (Solidity docs delegated Ballot): `giveRightToVote`, `vote` proved. `delegate`, `winningProposal`, `winnerName` unknown: loop leaves print with `‹…›` escapes; closer gaps for struct-member saves under quantifiers and `∃` witnesses. |
| `Examples/Benchmark/SolkeyMisc/FunctionModifier.lean` | solkey real-world `FunctionModifier`: constructor, `changeOwner` and recursive reentrancy-guarded `decrement` proved. |
| `Examples/Benchmark/SolkeyMisc/TimeLock.lean` | solkey real-world `TimeLock` (0.8 overflow port): `deposit`, `increaseLockTime` proved. `withdraw` refuted by a kernel run: a self-withdrawal books no net debit. |
| `Examples/Benchmark/SolkeyMisc/WETH9.lean` | solkey real-world `WETH9` (canonical WETH, 0.8 port): `deposit`, `approve` proved. `withdraw` unknown: the contract's own `transfer` shadows `address.transfer` in the front end. `transferFrom` unknown: closer exhausts heartbeats on consecutive mapping saves. |
