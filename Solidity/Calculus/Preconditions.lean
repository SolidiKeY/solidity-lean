import Solidity.Calculus.Logic

/-!
# The entry condition of an obligation

An entry check negates the antecedent of an implication under its leading
quantifiers and hidden parameter binders. It preserves their typed contexts and carries its origin
as a proof. Validity of that check certifies an impossible entry condition;
invalidity supplies a possible entry state. Unsupported shapes have no check.
This is independent of proving the program's postcondition.
-/

namespace Solidity

variable {C : Contract} {Γ : Ctx}

/-- The negation of the first implication's antecedent, under the same binders. -/
inductive Fml.EntryNegative : {Γ : Ctx} → Fml C Γ → Fml C Γ → Prop where
  | imp {Γ : Ctx} (pre post : Fml C Γ) : EntryNegative (.imp pre post) (.not pre)
  | all {Γ : Ctx} (x : Var) (p : PrimTy) {φ ψ : Fml C (.val p :: Γ)} :
      EntryNegative φ ψ → EntryNegative (.all x p φ) (.all x p ψ)
  | bind {Γ : Ctx} (m : Modality) (x : Var) (t : LTy) {φ ψ : Fml C (t :: Γ)} :
      EntryNegative φ ψ → EntryNegative (.bind m x t φ) (.bind m x t ψ)

/-- Extract an entry check together with its exact relationship to the source. -/
def Fml.entryNegative? : {Γ : Ctx} → (φ : Fml C Γ) → Option {ψ : Fml C Γ // EntryNegative φ ψ}
  | _, .imp pre post => some ⟨.not pre, .imp pre post⟩
  | _, .all x p body => do
    let ⟨check, h⟩ ← body.entryNegative?
    pure ⟨.all x p check, .all x p h⟩
  | _, .bind m x t body => do
    let ⟨check, h⟩ ← body.entryNegative?
    pure ⟨.bind m x t check, .bind m x t h⟩
  | _, _ => none
  termination_by structural _ φ => φ

/-- An impossible entry condition makes the original implication vacuous. -/
theorem Fml.EntryNegative.holds_source {φ ψ : Fml C Γ} (h : EntryNegative φ ψ)
    (σ : State C Γ) (empty : holds σ ψ) : holds σ φ := by
  induction h with
  | imp pre post =>
    simp only [holds] at empty ⊢
    exact fun hp => (empty hp).elim
  | all x p h ih =>
    simp only [holds] at empty ⊢
    intro v
    exact ih (σ.push v) (empty v)
  | bind m x t h ih =>
    simp only [holds, Modality.forallB] at empty ⊢
    intro v
    exact ih (σ.push v) (empty v)

/-- The source formula determines its check uniquely. -/
theorem Fml.EntryNegative.unique {φ ψ χ : Fml C Γ} (h : EntryNegative φ ψ)
    (h' : EntryNegative φ χ) : ψ = χ := by
  induction h with
  | imp pre post => cases h'; rfl
  | all x p h ih =>
    cases h' with
    | all _ _ h' => exact congrArg (Fml.all x p) (ih h')
  | bind m x t h ih =>
    cases h' with
    | bind _ _ _ h' => exact congrArg (Fml.bind m x t) (ih h')

/-- A kernel-checked certificate that no entry state meets the obligation's precondition. -/
def Fml.PreconditionsImpossible (φ : Fml C []) : Prop :=
  ∃ ψ, EntryNegative φ ψ ∧ Fml.Valid ψ

/-- A kernel-checked refutation of entry impossibility, hence a possible entry state. -/
def Fml.PreconditionsPossible (φ : Fml C []) : Prop :=
  ∃ ψ, EntryNegative φ ψ ∧ ¬ Fml.Valid ψ

theorem Fml.PreconditionsImpossible.valid {φ : Fml C []}
    (h : PreconditionsImpossible φ) : Fml.Valid φ := by
  obtain ⟨ψ, origin, empty⟩ := h
  exact fun σ => origin.holds_source σ (empty σ)

theorem Fml.PreconditionsImpossible.not_possible {φ : Fml C []}
    (h : PreconditionsImpossible φ) : ¬ PreconditionsPossible φ := by
  obtain ⟨ψ, origin, empty⟩ := h
  rintro ⟨χ, origin', nonempty⟩
  cases origin.unique origin'
  exact nonempty empty

end Solidity

/-- info: 'Solidity.Fml.PreconditionsImpossible.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Fml.PreconditionsImpossible.valid
/-- info: 'Solidity.Fml.PreconditionsImpossible.not_possible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Fml.PreconditionsImpossible.not_possible
