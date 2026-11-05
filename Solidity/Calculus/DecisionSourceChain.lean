import Solidity.Calculus.DecisionSourceInstance
import Solidity.Calculus.DeclarationReduction

/-! # Complete source literal-chain recognition and an exact preparation stage
The existing intrinsic chain parser is complete for its stated source family.
Its real result supplies an existing declaration-reduction certificate. This
consumer does not register a normalizer/decision route or discover parameters.
-/
namespace Solidity.Decide

/-- Every intrinsic chain is found at its actual supplied bound and literal. -/
theorem sourceUIntLiteralChain_complete {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} (w : SourceUIntLiteralChain bound value φ) :
    (sourceUIntLiteralChain? φ bound value).isSome = true := by
  induction w with
  | leaf w =>
    have hc : (sourceUIntLiteralInstance? _ bound value).isSome = true :=
      sourceUIntLiteralInstance_complete w
    rcases w with ⟨name, body, p, lhs, rhs, hv, hi, hφ⟩
    subst hφ
    change ((sourceUIntLiteralInstance? _ bound value).map SourceUIntLiteralChain.leaf).isSome = true
    rw [Option.isSome_map]
    exact hc
  | all name prim w ih =>
    change ((sourceUIntLiteralChain? _ bound value).map (SourceUIntLiteralChain.all name prim)).isSome = true
    rw [Option.isSome_map]
    exact ih

/-- Recognition returns the actual source-chain witness. -/
theorem sourceUIntLiteralChain_witness {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote}
    (h : (sourceUIntLiteralChain? φ bound value).isSome = true) :
    Nonempty (SourceUIntLiteralChain bound value φ) := by
  cases he : sourceUIntLiteralChain? φ bound value with
  | none => rw [he] at h; cases h
  | some w => exact ⟨w⟩

theorem sourceUIntLiteralChain_iff {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} :
    (sourceUIntLiteralChain? φ bound value).isSome = true ↔
      Nonempty (SourceUIntLiteralChain bound value φ) :=
  ⟨sourceUIntLiteralChain_witness, fun ⟨w⟩ => sourceUIntLiteralChain_complete w⟩

instance sourceUIntLiteralChain_decidable {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} :
    Decidable (Nonempty (SourceUIntLiteralChain bound value φ)) :=
  if h : (sourceUIntLiteralChain? φ bound value).isSome = true then
    isTrue (sourceUIntLiteralChain_witness h)
  else isFalse (fun w => h (sourceUIntLiteralChain_iff.mpr w))

/-- Exact normalization is derived from the computed all-left/substitution
chain, never from a validity oracle or a supplied completion certificate. -/
def sourceUIntLiteralReduction? {C : Contract} {Γ : Ctx} (φ : Fml C Γ)
    (bound value : PrimTy.uint.Denote) : Option (DeclarationReduction φ) :=
  (sourceUIntLiteralChain? φ bound value).map fun w =>
    DeclarationReduction.certified φ w.valid

theorem sourceUIntLiteralReduction_iff {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} :
    (sourceUIntLiteralReduction? φ bound value).isSome = true ↔
      Nonempty (SourceUIntLiteralChain bound value φ) := by
  simp only [sourceUIntLiteralReduction?, Option.isSome_map]
  exact sourceUIntLiteralChain_iff

/-- The actual preparation returns truth with pointwise equivalence at every
original typed state, retaining partial reads in the original formula. -/
theorem sourceUIntLiteralReduction_complete {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} (w : SourceUIntLiteralChain bound value φ) :
    ∃ r : DeclarationReduction φ, sourceUIntLiteralReduction? φ bound value = some r ∧
      r.formula = .tt ∧ ∀ σ : State C Γ, holds σ r.formula ↔ holds σ φ := by
  have hc : (sourceUIntLiteralChain? φ bound value).isSome = true := sourceUIntLiteralChain_complete w
  cases he : sourceUIntLiteralChain? φ bound value with
  | none => rw [he] at hc; cases hc
  | some found =>
    exact ⟨DeclarationReduction.certified φ found.valid,
      by simp only [sourceUIntLiteralReduction?, he, Option.map_some], rfl,
      (DeclarationReduction.certified φ found.valid).correct⟩

end Solidity.Decide
