| Module | Its examples |
|---|---|
| `Examples/RedTeam/Syntax/LiteralFolding.lean` | Red-team witness: literal expressions with `%`, `**` or `<<` run as `uint256` arithmetic (`7 % 2 / 2 * 2` returns `0`, `2 ** 256 - 1` reverts) where solc folds them exactly (`1`, `2^256 - 1`). |
| `Examples/RedTeam/Syntax/NegNegPrinter.lean` | Red-team witness: the program and clause printers write `-(-y)` as `--y`, a Solidity pre-decrement; runs of both programs from `y := 3` disagree. |
