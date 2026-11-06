import Solidity.Source.Infer
import Solidity.Frontend.Static.InferComplete

/-! Standalone H55 backfill against unchanged production inputs.
These are acceptance obligations for a future migration, not its implementation. -/
namespace H55.SourceRelations
open Solidity.Source
namespace F
abbrev infer := Solidity.Frontend.Static.infer
end F

theorem mapping_helper_exact (τ : STy) :
    τ.isMapping = Solidity.Frontend.Static.isMappingTy τ := rfl

theorem payable_helper_exact (τ : STy) :
    τ.isPayableArg = Solidity.Frontend.Static.payableArg τ := rfl

theorem location_helper_exact (τ : STy) :
    τ.convLoc = Solidity.Frontend.Static.convLoc τ := rfl

/-- A returned Option derivation has a type in the exhaustive checker.
This does not claim the exhaustive checker chooses that derivation first. -/
theorem option_success_list_type (Γ : Ctx) (e : Syn .expr) (r : Inferred Γ e)
    (_success : Typed.infer Γ e = some r) :
    r.1 ∈ Solidity.Frontend.Static.inferTys Γ e :=
  Solidity.Frontend.Static.typed_complete r.2

/-- Empty *typing* results refuse exactly the underivable expressions.
Auxiliary receiver results are deliberately not confused with typings. -/
theorem expression_refusal_iff (Γ : Ctx) (e : Syn .expr) :
    Solidity.Frontend.Static.inferTys Γ e = [] ↔ ∀ τ, ¬ HasType Γ e τ := by
  constructor
  · intro empty τ typed
    have member := Solidity.Frontend.Static.hasType_iff.mp typed
    rw [empty] at member
    exact List.not_mem_nil member
  · intro absent
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro τ member
    exact absent τ (Solidity.Frontend.Static.hasType_iff.mpr member)

/-- Exhaustive refusal propagates to the Option checker, for every fuel. -/
theorem list_refusal_option_refusal (Γ : Ctx) (e : Syn .expr)
    (empty : Solidity.Frontend.Static.inferTys Γ e = []) (fuel : Nat) :
    Typed.inferN fuel Γ e = none := by
  cases selected : Typed.inferN fuel Γ e with
  | none => rfl
  | some r => exact False.elim ((expression_refusal_iff Γ e).mp empty r.1 ⟨r.2⟩)

/-- Fuel zero is a computational refusal, never a completeness certificate. -/
theorem zero_fuel_bool_control (Γ : Ctx) :
    Typed.inferN 0 Γ (.lit (.bool true)) = none ∧
    HasType Γ (.lit (.bool true)) .bool := ⟨rfl, ⟨.bool true⟩⟩

#print axioms mapping_helper_exact
#print axioms payable_helper_exact
#print axioms location_helper_exact
#print axioms option_success_list_type
#print axioms expression_refusal_iff
#print axioms list_refusal_option_refusal
#print axioms zero_fuel_bool_control
end H55.SourceRelations
