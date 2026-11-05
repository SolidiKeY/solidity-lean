import Solidity.Calculus.ArrayProperty

/-!
# One-way negative-chain instantiation

Finite instances can prove a leaf independently of the array/memory floor
reconstruction needed for the converse. This proof interface is not an exact
Prep, a new decision branch, a coverage classifier or a Residue definition.
-/
namespace Solidity.Decide
variable {C : Contract} {K : PrimTy}

/-- Instantiate only negative quantifier-free chains of K, keeping the original
instantiator's definedness guards. No array-root or floor premise is needed. -/
def LFml.negativeChainInst (us : List (LTm C (.val K))) : Bool → LFml C → LFml C
  | pol, .not φ => .not (φ.negativeChainInst us (!pol))
  | pol, .and φ ψ => .and (φ.negativeChainInst us pol) (ψ.negativeChainInst us pol)
  | pol, .imp φ ψ => .imp (φ.negativeChainInst us (!pol)) (ψ.negativeChainInst us pol)
  | pol, .all k p φ =>
    if !pol && (LFml.all k p φ).chainQF K then (LFml.all k p φ).inst us else .all k p φ
  | _, φ => φ

/-- Positive instances imply the original; at negative polarity the original
implies its instances. These implications do not assert equivalence. -/
theorem LFml.negativeChainInst_sound (g : State C []) (us : List (LTm C (.val K))) :
    ∀ (φ : LFml C) (pol : Bool) (ν : AEnv),
      (pol = true → (φ.negativeChainInst us pol).holds g ν → φ.holds g ν) ∧
      (pol = false → φ.holds g ν → (φ.negativeChainInst us pol).holds g ν)
  | .not φ, pol, ν => by
    have ih := LFml.negativeChainInst_sound g us φ (!pol) ν
    cases pol
    · exact ⟨nofun, fun _ h h' => h (ih.1 rfl h')⟩
    · exact ⟨fun _ h h' => h (ih.2 rfl h'), nofun⟩
  | .and φ ψ, pol, ν => by
    have ih1 := LFml.negativeChainInst_sound g us φ pol ν
    have ih2 := LFml.negativeChainInst_sound g us ψ pol ν
    exact ⟨fun hp h => ⟨ih1.1 hp h.1, ih2.1 hp h.2⟩,
      fun hp h => ⟨ih1.2 hp h.1, ih2.2 hp h.2⟩⟩
  | .imp φ ψ, pol, ν => by
    have ih1 := LFml.negativeChainInst_sound g us φ (!pol) ν
    have ih2 := LFml.negativeChainInst_sound g us ψ pol ν
    cases pol
    · exact ⟨nofun, fun _ h h' => ih2.2 rfl (h (ih1.1 rfl h'))⟩
    · exact ⟨fun _ h h' => ih2.1 rfl (h (ih1.2 rfl h')), nofun⟩
  | .all k p φ, pol, ν => by
    refine ⟨fun hp h => ?_, fun hp h => ?_⟩
    · subst hp
      simpa only [LFml.negativeChainInst, Bool.not_true, Bool.false_and, if_false] using h
    · subst hp
      show LFml.holds g ν (if (!false && (LFml.all k p φ).chainQF K) = true then
        (LFml.all k p φ).inst us else .all k p φ)
      split
      · rename_i hb
        simp only [Bool.not_false, Bool.true_and] at hb
        exact LFml.inst_sound g us _ ν hb h
      · exact h
  | .tt, _, _ => ⟨fun _ h => h, fun _ h => h⟩
  | .eq _ _, _, _ => ⟨fun _ h => h, fun _ h => h⟩

/-- A valid finite instance is a sound proof of the original leaf, even where
no countermodel reconstruction or complete fragment is available. -/
theorem LFml.valid_of_negativeChainInst {φ : LFml C} (us : List (LTm C (.val K)))
    (h : (φ.negativeChainInst us true).Valid) : φ.Valid := by
  intro g ν
  exact (LFml.negativeChainInst_sound g us φ true ν).1 rfl (h g ν)

/-- Quantifier-free leaves are unchanged at either polarity. -/
theorem LFml.negativeChainInst_qf (us : List (LTm C (.val K))) :
    ∀ (φ : LFml C), φ.qfB = true → ∀ pol, φ.negativeChainInst us pol = φ
  | .tt, _, _ | .eq _ _, _, _ => rfl
  | .not φ, h, pol => congrArg LFml.not (LFml.negativeChainInst_qf us φ h (!pol))
  | .and φ ψ, h, pol => by
    simp only [LFml.qfB, Bool.and_eq_true] at h
    simp only [LFml.negativeChainInst, LFml.negativeChainInst_qf us φ h.1 pol,
      LFml.negativeChainInst_qf us ψ h.2 pol]
  | .imp φ ψ, h, pol => by
    simp only [LFml.qfB, Bool.and_eq_true] at h
    simp only [LFml.negativeChainInst, LFml.negativeChainInst_qf us φ h.1 (!pol),
      LFml.negativeChainInst_qf us ψ h.2 pol]
  | .all _ _ _, h, _ => by cases h

/-- A concrete client schema: a negative chain proves every guarded finite
instance, for arbitrary typed body contents, including fixed/nested reads. -/
theorem LFml.negativeChainInst_instance_client (us : List (LTm C (.val K)))
    (k : Nat) (φ : LFml C) (hc : (LFml.all k K φ).chainQF K = true) :
    (LFml.imp (.all k K φ) ((LFml.all k K φ).inst us)).Valid := by
  apply LFml.valid_of_negativeChainInst us
  intro g ν
  change ((LFml.all k K φ).negativeChainInst us false).holds g ν →
    (((LFml.all k K φ).inst us).negativeChainInst us true).holds g ν
  rw [LFml.negativeChainInst_qf us _ (LFml.qfB_inst us _ hc)]
  simp only [LFml.negativeChainInst, Bool.not_false, Bool.true_and, hc, if_true]
  exact fun h => h

end Solidity.Decide
