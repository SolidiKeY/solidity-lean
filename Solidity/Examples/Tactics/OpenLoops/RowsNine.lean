import Solidity.Examples.Tactics.OpenLoops.RowsNine.Finish

/-!
# `binomialRowsNine`, the nested-loop binomial over nine memory rows

The original walk is checked in 128-step chunks. Three continuation lemmas
checkpoint it after four iterations each, so no module elaborates the entire
walk under the slow library's per-module time cap. Each continuation is
kernel checked; the final theorem composes them without changing the problem.
-/

namespace Solidity.Examples.Tactics.OpenLoops
open scoped Solidity.Scoped

/-- `binomial(9, 5) == 70` over nine rows of memory arrays. -/
theorem binomialRowsNine : ⊢ Solc.SolcLoopsOpen.binomialRowsNine.problem := by
  exact RowsNine.Stage1.stage1 (RowsNine.Stage2.stage2 (RowsNine.Stage3.stage3 RowsNine.Finish.finish))

end Solidity.Examples.Tactics.OpenLoops
