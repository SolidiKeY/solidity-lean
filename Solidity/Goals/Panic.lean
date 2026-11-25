import Solidity.Goals.PanicRun
import Solidity.Goals.PanicProvenance
import Solidity.Goals.PanicSource

/-! Finish-line component 5: `Solidity.Semantics.run_panic_codes` (plan w3b-panic-bind). -/

namespace Solidity.Goals

@[goal Solidity.Semantics.run_panic_codes "w3b-panic-bind" ← panicRunOutcomes panicCodeProvenance panicSourceAssociation]
def runCarriesPanicCodes : Prop :=
  panicRunOutcomes ∧ panicCodeProvenance ∧ panicSourceAssociation

end Solidity.Goals
