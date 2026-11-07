import Solidity.Calculus.DecisionUIntRecognizer
import Solidity.Calculus.DecisionNumericCoverage

/-! # Decidable source syntax for the existing literal-linear uint grammar
The recognizer returns a derivation on the original intrinsic term. It does not
consult a decision verdict, Covered, lowering or a semantic validity oracle.
-/
namespace Solidity


namespace Decide

/-- Executable source checks feed the existing constructive coverage bridge. -/
theorem uintShapePrefix_Covered {C : Contract} (name : Var)
    (a b : Tm C [.val .uint] (.val .uint))
    (ha : a.uintLinearShape = true) (hb : b.uintLinearShape = true)
    (hs : a.size + b.size ≤ 71) : (primitivePrefixEq name a b).Covered = true :=
  uintPrefix_Covered name (a.uintLinearShape_sound ha) (b.uintLinearShape_sound hb) hs

/-- The accepted source class has certified results under the unchanged hash premise. -/
theorem uintShapePrefix_certified {C : Contract} (name : Var)
    (a b : Tm C [.val .uint] (.val .uint))
    (ha : a.uintLinearShape = true) (hb : b.uintLinearShape = true)
    (hs : a.size + b.size ≤ 71) :
    (decideGoal (primitivePrefixEq name a b) = .proved ∧ Fml.ValidH (primitivePrefixEq name a b)) ∨
      ∃ σ : State C [], decideGoal (primitivePrefixEq name a b) = .refuted σ ∧
        ¬ Fml.holdsH σ (primitivePrefixEq name a b) :=
  uintPrefix_certified name (a.uintLinearShape_sound ha) (b.uintLinearShape_sound hb) hs

end Decide
end Solidity
