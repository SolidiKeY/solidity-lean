import Solidity.Goals.Finish
import Solidity.Theorems
import Solidity.Backend.CompilerEndpoint
import Solidity.Hash.CompilerCorrect.Prefix
import Solidity.Calculus.RuleShapes
import Solidity.Backend.CompilerTotal

/-! The finish line assembled from its two open components (plan step
fl0-finish-assembly, H798). The five components proved on master are applied as
their goals name them; `lowerLoopsCorrect` and `runCarriesPanicCodes` enter as the
goal constants themselves and are never unfolded, so this theorem survives their
statement. This is not the finish claim `Solidity.Finish.project_finished`. -/

namespace Solidity.Finish

/-- `projectFinished`, given the two components still open on master. -/
theorem project_finished_of_open (hLoops : Solidity.Goals.lowerLoopsCorrect)
    (hPanic : Solidity.Goals.runCarriesPanicCodes) : Solidity.Goals.projectFinished :=
  ⟨fun hP hm hL => Solidity.Main.compiler_correct hP hm hL,
    Solidity.Backend.compiler_endpoint_correct, hLoops,
    Solidity.Hash.compiler_correct_collisionFree, hPanic,
    Solidity.RuleShapes.taclets_partitioned, Solidity.Backend.compiler_total⟩

end Solidity.Finish
