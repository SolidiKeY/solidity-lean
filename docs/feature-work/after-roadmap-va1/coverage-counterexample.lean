import Solidity.Calculus.Decision
import Solidity.Calculus.Notation

namespace Solidity.Scratch.VA1CoverageProbe
open Solidity.Decide
def Bank : Contract := contract!{ uint value; }
local instance : InContract := ⟨Bank⟩
/-- A program-free source product whose constant factor folds during preparation. -/
def deadProduct : Fml Bank [] :=
  dl[Bank]{ ∀ uint x; (1 + 1) * x = x + x }
#eval deadProduct.inTarget {}
#eval deadProduct.Covered
theorem deadProduct_not_target : deadProduct.inTarget {} = false := by decide +kernel
theorem deadProduct_covered : deadProduct.Covered = true := by decide +kernel
#print axioms deadProduct_not_target
#print axioms deadProduct_covered
end Solidity.Scratch.VA1CoverageProbe
