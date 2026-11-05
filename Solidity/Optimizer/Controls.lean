import Solidity.Optimizer.Laws
import Solidity.Optimizer.RoadmapComposition

/-!
# O01 framework controls

Scalar equality controls test the validator trust boundary, not EVM or D6.
Intrinsic witnesses exercise existing nonempty typed syntax. They do not claim
that an identity pass or a reject-all validator implements O02/O03.
-/
namespace Solidity.Optimizer.Controls

/-- Accepting control: the executable checker admits an equal pair. -/
theorem equal_accepted : (Validator.equality Nat).validate 37 37 = true := rfl

/-- Negative control: an unequal proposal is rejected. -/
theorem changed_rejected : (Validator.equality Nat).validate 37 38 = false := rfl

/-- The rejected untrusted proposal cannot change the executable result. -/
theorem changed_fallback : validated (Validator.equality Nat) Nat.succ 37 = 37 := rfl

/-- Soundness implies that no checker for equality can admit this mutation. -/
theorem no_sound_checker_accepts (validator : Validator (fun p q : Nat => p = q)) :
    validator.validate 37 38 = false :=
  validator.rejects_unsound (by decide)

/-- Nonempty intrinsic Yul syntax at fixed signatures/externals/control/locals. -/
def yulWitness : Solidity.Yul.Stmt [] [] ⟨false, false⟩ 0 :=
  .seq .skip (.seq .skip .skip)

/-- A rejected proposal returns that exact intrinsic program. -/
theorem yul_fallback (proposal : Pass (Solidity.Yul.Stmt [] [] ⟨false, false⟩ 0)) :
    validated (Validator.reject Eq) proposal yulWitness = yulWitness := rfl

/-- An inhabited intrinsic lowering context, without any source-language stub. -/
def loweringWitness (C : Contract) (Γ : Ctx) : Solidity.Prog C Γ Γ :=
  .cons .assumeFalse .nil

/-- Identity preserves the full typed syntax, a stronger framework-only relation. -/
theorem lowering_identity (C : Contract) (Γ : Ctx) :
    Preserves Eq (fun p : Solidity.Prog C Γ Γ => p) := fun _ => rfl

/-- Composition with two guarded proposals remains certified for equality. -/
theorem combination (first second : Pass Nat) :
    Preserves Eq ((validated (Validator.equality Nat) first).comp
      (validated (Validator.equality Nat) second)) :=
  (validated_preserves (fun _ => rfl) (Validator.equality Nat) first).comp
    (fun a b => a.trans b)
    (validated_preserves (fun _ => rfl) (Validator.equality Nat) second)

#print axioms asRoadmapPass
#print axioms beforeCompilation
#print axioms validate_sound
#print axioms validated_preserves
#print axioms Preserves.comp
#print axioms no_sound_checker_accepts
#print axioms combination

end Solidity.Optimizer.Controls
