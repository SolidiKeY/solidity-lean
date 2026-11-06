import Solidity.Examples.Tactics.OpenLoops

/-!
# `binomialRowsNine`, the nested-loop binomial over nine memory rows

The slowest obligation of `Examples/Tactics/OpenLoops.lean`, in its own module
so that each module stays within the pre-gate bounds: its walk of about two
thousand steps is checked in chunks of 128 (`sol_prove (chunk := n)`,
`Calculus/ProveChunked.lean`).
-/

namespace Solidity.Examples.Tactics.OpenLoops
open scoped Solidity.Scoped

/-- `binomial(9, 5) == 70` over nine rows of memory arrays. -/
theorem binomialRowsNine : ⊢ Solc.SolcLoopsOpen.binomialRowsNine.problem := by
  sol_prove (chunk := 128)

end Solidity.Examples.Tactics.OpenLoops
