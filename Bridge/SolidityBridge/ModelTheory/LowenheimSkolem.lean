import SolidityBridge.ModelTheory
import Mathlib.ModelTheory.Skolem

/-!
Löwenheim–Skolem for the contract theory. Smaller elementary submodels
preserve all translated first-order leaves. Conversely the theory has models
at every infinite cardinal at least the language cardinal. Such abstract
models need not be the carrier of a concrete Solidity state.
-/
namespace Solidity.FO

open FirstOrder FirstOrder.Language Cardinal

variable {C : Contract}

instance carrier_infinite (g : State C []) : Infinite (Carrier C g) := by
  apply Infinite.of_injective (fun z : Int => Carrier.mk .kint (z, none))
  intro x y h
  have he : (Carrier.mk .kint (x, none) : Carrier C g).as .kint =
      (Carrier.mk .kint (y, none) : Carrier C g).as .kint := congrArg (Carrier.as .kint) h
  simp only [Carrier.as_mk, Option.some.injEq, Prod.mk.injEq, and_true] at he
  exact he

/-- No infinite-cardinality hypothesis about the theory is assumed: a
concrete state's unbounded logical integers supply an infinite model. -/
theorem solTheory_models_of_card (κ : Cardinal.{0}) (hinf : ℵ₀ ≤ κ)
    (hlang : (lang C).card ≤ κ) :
    ∃ M : Theory.ModelType.{0, 0, 0} (SolTheory C), #M = κ := by
  apply Theory.exists_model_card_eq
    (T := SolTheory C) (κ := κ) ?_ hinf (by simpa only [Cardinal.lift_id] using hlang)
  refine ⟨Theory.ModelType.of (SolTheory C) (Carrier C (State.init C)), ?_⟩
  change Infinite (Carrier C (State.init C))
  infer_instance

/-- Compactness for additional storage assumptions, retaining all contract
axioms at each finite stage. -/
theorem solTheory_compact (facts : (lang C).Theory) :
    (SolTheory C ∪ facts).IsSatisfiable ↔
      ∀ F : Finset (lang C).Sentence, (F : (lang C).Theory) ⊆ facts →
        (SolTheory C ∪ (F : (lang C).Theory)).IsSatisfiable := by
  classical
  constructor
  · intro h F hF
    exact h.mono (Set.union_subset_union_right (SolTheory C) hF)
  · intro h
    rw [Theory.isSatisfiable_iff_isFinitelySatisfiable]
    intro T hT
    let F := T.filter (· ∈ facts)
    have hf : (F : (lang C).Theory) ⊆ facts := fun _ hφ => (Finset.mem_filter.mp hφ).2
    apply (h F hf).mono
    intro φ hφ
    rcases hT hφ with hc | hs
    · exact Or.inl hc
    · exact Or.inr (Finset.mem_filter.mpr ⟨hφ, hs⟩)

/-- Downward Löwenheim–Skolem, retaining any requested set of parameters
and the whole contract theory. Cardinality assumptions are explicit. -/
theorem solTheory_elementary_submodel (M : Theory.ModelType.{0, 0, 0} (SolTheory C))
    (parameters : Set M) (κ : Cardinal.{0}) (hinf : ℵ₀ ≤ κ)
    (hparams : #parameters ≤ κ) (hlang : (lang C).card ≤ κ) (hmodel : κ ≤ #M) :
    ∃ S : (lang C).ElementarySubstructure M,
      parameters ⊆ S ∧ #S = κ ∧ S ⊨ SolTheory C := by
  obtain ⟨S, hs, hc⟩ := (lang C).exists_elementarySubstructure_card_eq parameters κ hinf
    (by simpa only [Cardinal.lift_id] using hparams)
    (by simpa only [Cardinal.lift_id] using hlang)
    (by simpa only [Cardinal.lift_id] using hmodel)
  exact ⟨S, hs, by simpa only [Cardinal.lift_id] using hc, inferInstance⟩

/-- An elementary submodel of a concrete state preserves each translated
closed first-order formula, whether or not the formula is valid in all states. -/
theorem holds_iff_submodel_realize (g : State C [])
    (S : (lang C).ElementarySubstructure (Carrier C g))
    {φ : Fml C []} {ψ : (lang C).Sentence} (h : φ.toBF = some ψ) :
    holds g φ ↔ S ⊨ ψ := by
  rw [S.realize_sentence]
  exact holds_iff_realize g h

end Solidity.FO

/-- info: 'Solidity.FO.solTheory_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.FO.solTheory_compact

/-- info: 'Solidity.FO.solTheory_models_of_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.FO.solTheory_models_of_card

/-- info: 'Solidity.FO.solTheory_elementary_submodel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.FO.solTheory_elementary_submodel

/-- info: 'Solidity.FO.holds_iff_submodel_realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.FO.holds_iff_submodel_realize
