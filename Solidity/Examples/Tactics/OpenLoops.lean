import Solidity.Frontend.Import
import Solidity.Frontend.Problems
import Solidity.Calculus.Closers
import Solidity.Calculus.ProveChunked

/-!
# Formerly open solc loop obligations

The pinned source is the original `SolcLoopsOpen` port. Memory observations
are reduced when formed, before subsequent writes can duplicate their trees,
and an identity a copy mints names the copies below it without the writes
between them where those writes provably land (`copyRes`,
`Calculus/MemRead.lean`), so the rows a later row reads stay the size of
the allocations, not of the history.

`binomialRowsNine` unrolls about two thousand steps of nested loops: its walk
is checked in chunks of 128 steps (`sol_prove (chunk := n)`,
`Calculus/ProveChunked.lean`), each chunk and its leaf under the ordinary
heartbeat budget.  It is the slowest proof here, about four minutes.
-/

solc_import "../../../tests/solc/OpenLoops.ast.json" hash 0xd0e67a270c5e5bbf as Solc.SolcLoopsOpen
/-- info: 4 obligations declared scoped -/
#guard_msgs in
solc_scoped_problems Solc.SolcLoopsOpen

namespace Solidity.Examples.Tactics.OpenLoops
open scoped Solidity.Scoped

/-- The actual nested-array binomial source, with chained assignment and its loops. -/
theorem binomialFaithfulRowsSmall : ⊢ Solc.SolcLoopsOpen.binomialFaithfulRowsSmall.problem := by
  sol_prove

/-- `binomial(9, 5) == 70` over nine rows of memory arrays. -/
theorem binomialRowsNine : ⊢ Solc.SolcLoopsOpen.binomialRowsNine.problem := by
  sol_prove (chunk := 128)

end Solidity.Examples.Tactics.OpenLoops
