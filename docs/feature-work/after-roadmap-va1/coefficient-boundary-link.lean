import Solidity.Calculus.DecisionCoefficientBoundary
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


namespace Solidity.Scratch.VA1CoverageProbe
open Solidity.Decide Solidity.Decide.CoefficientBoundary

/-- The exact retained source witness is a member of the quantified coefficient family. -/
theorem retained_family_eq : deadProduct = coefficientLeaf
    (.app2 (.binop .add rfl) (.app0 (.lit (uintOfNat 1))) (.app0 (.lit (uintOfNat 1)))) := by
  rfl

/-- The generic boundary applies to the exact retained witness, without a new premise. -/
theorem retained_family_boundary : deadProduct.inTarget {} =
    (Tm.app2 (.binop .add rfl) (.app0 (.lit (uintOfNat 1)))
      (.app0 (.lit (uintOfNat 1))) : Tm Bank [] (.val .uint)).isLitV := by
  rw [retained_family_eq]
  exact coefficientLeaf_inTarget {} _

#print axioms retained_family_eq
#print axioms retained_family_boundary
end Solidity.Scratch.VA1CoverageProbe
