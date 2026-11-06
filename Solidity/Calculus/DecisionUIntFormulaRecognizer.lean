import Solidity.Calculus.DecisionUIntFormula
import Solidity.Calculus.DecisionUIntRecognizer

/-! # Constructive recognition of the existing numeric source formula grammar
This decides only QFUIntLinear membership by intrinsic constructors. It does
not inspect target, coverage, parser success or a verdict, and is not Residue.
-/
namespace Solidity

/-- Positive and negative evidence for the unchanged source-syntax predicate. -/
def Fml.qfUIntLinearDecidable {C : Contract} {Γ : Ctx}
    (φ : Fml C Γ) : Decidable φ.QFUIntLinear := by
  apply @Fml.casesOn C (fun Γ φ => Decidable φ.QFUIntLinear) Γ φ
  · intro Γ
    exact .isTrue .tt
  · intro Γ p a b
    cases p with
    | uint =>
      exact match (inferInstance : Decidable a.UIntLinear),
          (inferInstance : Decidable b.UIntLinear) with
        | .isTrue ha, .isTrue hb => .isTrue (.eq ha hb)
        | .isFalse ha, _ => .isFalse (fun h => match h with | .eq hA _ => ha hA)
        | _, .isFalse hb => .isFalse (fun h => match h with | .eq _ hB => hb hB)
    | bool | int => exact .isFalse (fun h => nomatch h)
  · intros
    exact .isFalse (fun h => nomatch h)
  · intro Γ φ
    exact match Fml.qfUIntLinearDecidable φ with
      | .isTrue hφ => .isTrue (.not hφ)
      | .isFalse hφ => .isFalse (fun h => match h with | .not hA => hφ hA)
  · intro Γ φ ψ
    exact match Fml.qfUIntLinearDecidable φ, Fml.qfUIntLinearDecidable ψ with
      | .isTrue hφ, .isTrue hψ => .isTrue (.and hφ hψ)
      | .isFalse hφ, _ => .isFalse (fun h => match h with | .and hA _ => hφ hA)
      | _, .isFalse hψ => .isFalse (fun h => match h with | .and _ hB => hψ hB)
  · intro Γ φ ψ
    exact match Fml.qfUIntLinearDecidable φ, Fml.qfUIntLinearDecidable ψ with
      | .isTrue hφ, .isTrue hψ => .isTrue (.imp hφ hψ)
      | .isFalse hφ, _ => .isFalse (fun h => match h with | .imp hA _ => hφ hA)
      | _, .isFalse hψ => .isFalse (fun h => match h with | .imp _ hB => hψ hB)
  all_goals intros; exact .isFalse (fun h => nomatch h)
termination_by structural φ

instance Fml.instDecidableQFUIntLinear {C : Contract} {Γ : Ctx}
    (φ : Fml C Γ) : Decidable φ.QFUIntLinear := φ.qfUIntLinearDecidable

/-- A constructor-only Boolean view of the existing grammar, not a coverage test. -/
def Fml.qfUIntLinearShape {C : Contract} {Γ : Ctx} (φ : Fml C Γ) : Bool :=
  @decide φ.QFUIntLinear φ.qfUIntLinearDecidable

end Solidity
