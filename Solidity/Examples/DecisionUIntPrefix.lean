import Solidity.Calculus.DecisionUIntPrefix
import Solidity.Examples.DecisionUIntBridge

/-! # Actual positive-prefix pipeline controls
The source-grammar fact is about the reducer body before preparation.
These controls do not assert an exhaustive target/coverage boundary. -/
namespace Solidity.Examples.DecisionUIntPrefix
open Solidity.Decide
open Solidity.Examples.DecisionUIntBridge
open Solidity.Examples.DecisionCoefficientBoundary (Bank directTwo directTwo_validH directTwo_proved)
set_option Elab.async false

/-- The non-total operands retain the actual initial prefix variable zero. -/
theorem partial_source_exact :
    (sourceReduction? partialLeaf).map (·.leaf) =
      some (.all 0 .uint (LFml.optEq (lowered 1) (lowered 2))) := by rfl

theorem partial_prepared_exact : leafOf? partialLeaf =
    some (LFml.all 0 .uint (LFml.optEq (lowered 1) (lowered 2))).elim.condSimp.prenex :=
  leafOf_of_normalized_source partialLeaf _
    (primitivePrefixEq_normalizes (.user "x") decrement1 decrement2) partial_source_exact

theorem partial_constructive_source : ∃ ψ : LFml Bank,
    (sourceReduction? partialLeaf).map (·.leaf) = some (.all 0 .uint ψ) ∧
    ψ.Src false true :=
  uintPrefix_sourceReduction (.user "x") decrement1_grammar decrement2_grammar

/-- Reuse the inhabited semantic countermodel and certified actual refutation. -/
theorem partial_negative : ¬ Fml.Valid partialLeaf ∧ ∃ σ : State Bank [],
    decideGoal partialLeaf = .refuted σ ∧ ¬ Fml.holdsH σ partialLeaf :=
  ⟨partialLeaf_notValid, partialLeaf_refuted⟩

def rightMul : Tm Bank [.val .uint] (.val .uint) :=
  .app2 (.binop .mul rfl) current (.app0 (.lit (uintOfNat 2)))
def doubled : Tm Bank [.val .uint] (.val .uint) :=
  .app2 (.binop .add rfl) current current

theorem rightMul_grammar : rightMul.UIntLinear := .mulR _ current_grammar
theorem doubled_grammar : doubled.UIntLinear := .add current_grammar current_grammar

theorem rightMul_prepared : ∃ ψ : LFml Bank,
    leafOf? (primitivePrefixEq (.user "r") rightMul doubled) =
      some (LFml.all 0 .uint ψ).elim.condSimp.prenex ∧ ψ.Src false true :=
  uintPrefix_leafOf (.user "r") rightMul_grammar doubled_grammar

def leftMul : Tm Bank [.val .uint] (.val .uint) :=
  .app2 (.binop .mul rfl) (.app0 (.lit (uintOfNat 2))) current

theorem leftMul_grammar : leftMul.UIntLinear := .mulL _ current_grammar

theorem directTwo_prefix : directTwo = primitivePrefixEq (.user "x") leftMul doubled := rfl

theorem directTwo_prepared : ∃ ψ : LFml Bank,
    leafOf? directTwo = some (LFml.all 0 .uint ψ).elim.condSimp.prenex ∧ ψ.Src false true := by
  rw [directTwo_prefix]
  exact uintPrefix_leafOf (.user "x") leftMul_grammar doubled_grammar

theorem inhabited_positive : decideGoal directTwo = .proved ∧ Fml.ValidH directTwo :=
  ⟨directTwo_proved, directTwo_validH⟩

def unusedTerm : Tm Bank [.val .uint] (.val .uint) := .app0 (.lit (uintOfNat 2))

theorem unusedBinder_prepared : ∃ ψ : LFml Bank,
    leafOf? (primitivePrefixEq (.user "unused") unusedTerm unusedTerm) =
      some (LFml.all 0 .uint ψ).elim.condSimp.prenex ∧ ψ.Src false true :=
  uintPrefix_leafOf (.user "unused") (.lit _) (.lit _)

theorem missing_local_refusal : current.toL missingScope = none := missing_lookup

theorem nonlinear_outside : ¬ nonlinear.UIntLinear := nonlinear_outside_grammar

end Solidity.Examples.DecisionUIntPrefix
