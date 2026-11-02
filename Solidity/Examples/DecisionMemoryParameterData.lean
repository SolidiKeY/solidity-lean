import Solidity.Examples.DecisionGapData
import Solidity.Calculus.Surface

/-! The existing memory-parameter fixture, independently of its later verdict
and heap-model controls. Its original qualified declaration is retained. -/
namespace Solidity.Examples.Decision
local instance memoryParameterDataContract : InContract := ⟨Gaps⟩
open scoped Solidity.Scoped
set_option Elab.async false

/-- A repeated Theory read is equal even at an unset memory parameter. -/
def memParamSame : Fml Gaps [] :=
  dl![.box]{ s[0] = s[0] where uint[] memory s }

end Solidity.Examples.Decision
