import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! Changing only a branch label leaves the rule's intrinsic premise identical.
The universal certificate covers every contract, context, condition, modality
and fresh counter. This is an equivalence control, not a killed mutant. -/
namespace H28.GuardEquivalent
open Solidity

def original {C : Contract} {Γ : Ctx} (se : Simple C Γ .bool) : Premise C Γ Γ :=
  .split .capture (.isBool se.lower true) (.isBool se.lower false)
    .nil (.cons .revert .nil)

/-- The actual changed-label constructor retains this premise on every input. -/
theorem source_link_all {C : Contract} {Γ : Ctx} (k : Nat) (m : Modality)
    (se : Simple C Γ .bool) :
    Taclet C k m (.require (.simple se)) (original se) := .requireSimple

/-- Equality to the unchanged dispatcher premise gives semantic equality,
including every continuation, frames and postcondition. -/
theorem equivalence_all {C : Contract} {Γ : Ctx} (k : Nat) (m : Modality)
    (se : Simple C Γ .bool) {Δ Ω : Ctx} (rest : Prog C Γ Δ)
    (frames : Frames C Δ Ω) (post : Fml C Ω) :
    (original se).fml m rest frames post =
      (requireStep k (.simple se)).fml m rest frames post := by rfl

/-- The universal certificate has a concrete inhabited input. -/
theorem input_inhabited : Nonempty (State ({ vars := [] } : Contract) []) :=
  ⟨.init _⟩

#print axioms source_link_all
#print axioms equivalence_all
#print axioms input_inhabited
set_option pp.fullNames true
#check @source_link_all
#check @equivalence_all
#check @input_inhabited
end H28.GuardEquivalent
