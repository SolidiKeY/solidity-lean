import Solidity.Examples.Tactics.OpenLoops.RowsNine.Stage3

/-! # Close the remaining nine-row walk after the third checkpoint. -/
namespace Solidity.Examples.Tactics.OpenLoops.RowsNine.Finish

/-- The remaining obligation of the original nine-row binomial walk. -/
theorem finish : Stage3.stage3Goal := by
  rows_nine_finish

end Solidity.Examples.Tactics.OpenLoops.RowsNine.Finish
