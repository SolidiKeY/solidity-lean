import Solidity.Optimizer.Laws
import Solidity.Optimizer.RoadmapComposition

namespace Solidity.Optimizer.Controls

theorem equal_accepted : (Validator.equality Nat).validate 37 37 = true := rfl

theorem changed_rejected : (Validator.equality Nat).validate 37 38 = false := rfl

theorem changed_fallback : validated (Validator.equality Nat) Nat.succ 37 = 37 := rfl

theorem no_sound_checker_accepts (validator : Validator (fun p q : Nat => p = q)) :
    validator.validate 37 38 = false :=
  validator.rejects_unsound (by decide)

def yulWitness : Solidity.Yul.Stmt [] [] ⟨false, false⟩ 0 :=
  .seq .skip (.seq .skip .skip)

theorem yul_fallback (proposal : Pass (Solidity.Yul.Stmt [] [] ⟨false, false⟩ 0)) :
    validated (Validator.reject Eq) proposal yulWitness = yulWitness := rfl

def loweringWitness (C : Contract) (Γ : Ctx) : Solidity.Prog C Γ Γ :=
  .cons .assumeFalse .nil

theorem lowering_identity (C : Contract) (Γ : Ctx) :
    Preserves Eq (fun p : Solidity.Prog C Γ Γ => p) := fun _ => rfl

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
