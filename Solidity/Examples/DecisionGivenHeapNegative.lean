import Solidity.Calculus.DecisionGivenHeapExtension
import Solidity.Calculus.Surface
import Solidity.Examples.Decision

/-! # Non-reflexive given-heap control
Different literal keys must not inherit the all-heap reflexivity certificate.
This tests actual source recognition, independently of the finite candidate heap.
-/
namespace Solidity.Examples.DecisionGivenHeapNegative
open Solidity.Decide Solidity.Decide.ResidueReason Solidity.Examples.Decision
local instance : InContract := ⟨Gaps⟩
open scoped Solidity.Scoped
set_option Elab.async false

def unequalKeys : Fml Gaps [] := dl![.box]{ x[0] = x[1] where uint[] memory x }
def sameKey : Fml Gaps [] := dl![.box]{ x[0] = x[0] where uint[] memory x }

/-- Distinct source keys reject reflexivity; the matched control is inhabited. -/
theorem source_controls : unequalKeys.givenHeapLiteralReadReflexive = false ∧
    sameKey.givenHeapLiteralReadReflexive = true := by
  decide +kernel

/-- The positive control carries the actual all-heap certificate. -/
theorem sameKey_validH : Fml.ValidH sameKey :=
  ((givenHeapLiteralRead? sameKey).get source_controls.2).validH

end Solidity.Examples.DecisionGivenHeapNegative
