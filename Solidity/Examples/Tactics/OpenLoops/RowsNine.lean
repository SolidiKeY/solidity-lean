import Solidity.Examples.Tactics.OpenLoops

/-!
# `binomialRowsNine`, the nested-loop binomial over nine memory rows

The slowest obligation of `Examples/Tactics/OpenLoops.lean`, in its own module:
its walk of about two thousand steps is checked in chunks
(`sol_prove (chunk := n)`, `Calculus/ProveChunked.lean`). Each chunk's kernel
check re-reads the context it starts from, which grows with every chunk, so
fewer, larger chunks are faster. At `LEAN_NUM_THREADS=1` on a 4-core VM
(2026-11-09): chunks of 64 took 792 s at a 5849 MiB peak, over the slow
library's 600 s per-module CI budget (H134); chunks of 96 took 567 s at
8994 MiB; chunks of 128 take 531 s at 8945 MiB, under the 12 GiB pre-gate
cap. The 300 s default bound needs the walk checkpointed across modules,
which `sol_prove (chunk := n)` does not offer yet.
-/

namespace Solidity.Examples.Tactics.OpenLoops
open scoped Solidity.Scoped

/-- `binomial(9, 5) == 70` over nine rows of memory arrays. -/
theorem binomialRowsNine : ⊢ Solc.SolcLoopsOpen.binomialRowsNine.problem := by
  sol_prove (chunk := 128)

end Solidity.Examples.Tactics.OpenLoops
