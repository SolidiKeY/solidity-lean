import Solidity.Goals.Headline
import Solidity.Goals.Endpoint
import Solidity.Goals.Loops
import Solidity.Goals.Hash
import Solidity.Goals.Panic
import Solidity.Goals.Taclets

/-! The finish line (coordinator proposal 2026-11-09; changed only by decision): the
project is done when all six components hold. Each component lives in its own module,
owned by the lane that states or proves it. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Finish.project_finished "fl-finish-line" ← headlineIsNoPaymentRevert
    compilerEndpointCorrect lowerLoopsCorrect compilerCorrectCollisionFree
    runCarriesPanicCodes tacletsPartitioned]
def projectFinished : Prop :=
  headlineIsNoPaymentRevert ∧ compilerEndpointCorrect ∧ lowerLoopsCorrect ∧
    compilerCorrectCollisionFree ∧ runCarriesPanicCodes ∧ tacletsPartitioned

end Solidity.Goals
