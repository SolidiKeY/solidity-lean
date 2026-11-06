import Solidity.Examples.Tactics.OpenLoops

/-!
# `binomialRowsNine`, the nested-loop binomial over nine memory rows

The slowest obligation of `Examples/Tactics/OpenLoops.lean`, in its own module:
its walk of about two thousand steps is checked in chunks
(`sol_prove (chunk := n)`, `Calculus/ProveChunked.lean`). At
`LEAN_NUM_THREADS=1`, chunks of 128 peaked at 8992 MiB and 457 s, over the
8 GiB pre-gate bound; chunks of 64 peak at 5876 MiB but take 594 s. The
300 s bound needs the walk checkpointed across modules, which
`sol_prove (chunk := n)` does not offer yet.
-/

namespace Solidity.Examples.Tactics.OpenLoops
open scoped Solidity.Scoped

/-- `binomial(9, 5) == 70` over nine rows of memory arrays. -/
theorem binomialRowsNine : ⊢ Solc.SolcLoopsOpen.binomialRowsNine.problem := by
  sol_prove (chunk := 64)

end Solidity.Examples.Tactics.OpenLoops
