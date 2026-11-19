import Solidity.Tools.Goal

/-! The plan goal `benchmarkBudgetsMet` (`vu1-benchmarks`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Bench.budgets_met "vu1-benchmarks"]
def benchmarkBudgetsMet : Prop := Unstated

end Solidity.Goals
