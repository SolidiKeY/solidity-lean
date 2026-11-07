import tests.h62.item1.«infer-helpers».Shared
import Solidity.Source.Infer
import Solidity.Frontend.Static.Infer

/-!
Guarded regression: extracting the mapping, payable-argument and conversion-location
helpers must preserve all three production observations for every source type.
The mapping test remains shallow and the conversion default remains memory.
These pointwise lemmas change neither inferencer nor their existing statements;
they do not assert equivalence of the full inference algorithms.
-/
namespace Solidity.H62.InferHelpers.SharedAgreement

open Solidity.Source

/-- All shared observations agree simultaneously with the source helpers. -/
theorem source_observations (τ : STy) :
    Shared.isMapping τ = τ.isMapping ∧
    Shared.payableArg τ = τ.isPayableArg ∧
    Shared.convLoc τ = τ.convLoc := by
  cases τ <;> exact ⟨rfl, rfl, rfl⟩

/-- The same shared observations agree with the independent static helpers. -/
theorem static_observations (τ : STy) :
    Shared.isMapping τ = Solidity.Frontend.Static.isMappingTy τ ∧
    Shared.payableArg τ = Solidity.Frontend.Static.payableArg τ ∧
    Shared.convLoc τ = Solidity.Frontend.Static.convLoc τ := by
  cases τ <;> exact ⟨rfl, rfl, rfl⟩

theorem source_mapping (τ : STy) : Shared.isMapping τ = τ.isMapping :=
  (source_observations τ).1

theorem source_payable (τ : STy) : Shared.payableArg τ = τ.isPayableArg :=
  (source_observations τ).2.1

theorem source_location (τ : STy) : Shared.convLoc τ = τ.convLoc :=
  (source_observations τ).2.2

theorem static_mapping (τ : STy) :
    Shared.isMapping τ = Solidity.Frontend.Static.isMappingTy τ :=
  (static_observations τ).1

theorem static_payable (τ : STy) :
    Shared.payableArg τ = Solidity.Frontend.Static.payableArg τ :=
  (static_observations τ).2.1

theorem static_location (τ : STy) :
    Shared.convLoc τ = Solidity.Frontend.Static.convLoc τ :=
  (static_observations τ).2.2

#print axioms source_observations
#print axioms static_observations
#print axioms source_mapping
#print axioms source_payable
#print axioms source_location
#print axioms static_mapping
#print axioms static_payable
#print axioms static_location
end Solidity.H62.InferHelpers.SharedAgreement
