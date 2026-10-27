import Solidity.Calculus.Logic

/-!
# Finite equality-membership

The primitive type is an index of every operand. Membership is equality to
one of the listed terms, using the existing Theory equality. In particular,
this does not add a definedness condition for expressions that halt.
-/

namespace Solidity

variable {C : Contract} {Γ : Ctx} {p : PrimTy}

/-- Equality to any listed term; duplicates have no additional meaning. -/
def Fml.finiteMember (key : Tm C Γ (.val p)) (items : List (Tm C Γ (.val p))) : Fml C Γ :=
  items.foldr (fun item rest => .not (.and (.not (.eq key item)) (.not rest))) (.not .tt)

/-- The generated formula is exactly finite membership under Theory equality. -/
theorem holds_finiteMember (σ : State C Γ) (key : Tm C Γ (.val p))
    (items : List (Tm C Γ (.val p))) :
    holds σ (Fml.finiteMember key items) ↔
      ∃ item, item ∈ items ∧ key.denote σ = item.denote σ := by
  induction items with
  | nil =>
    change (¬ True) ↔ ∃ item, item ∈ ([] : List (Tm C Γ (.val p))) ∧ _
    simp only [List.not_mem_nil, false_and, exists_false, not_true_eq_false]
  | cons item items ih =>
    change (¬ (¬ (key.denote σ = item.denote σ) ∧
      ¬ holds σ (Fml.finiteMember key items))) ↔ _
    rw [ih]
    simp only [List.mem_cons]
    classical
    constructor
    · intro h
      by_cases eq : key.denote σ = item.denote σ
      · exact ⟨item, Or.inl rfl, eq⟩
      · have tail : ¬ ¬ ∃ other, other ∈ items ∧ key.denote σ = other.denote σ :=
          fun absent => h ⟨eq, absent⟩
        obtain ⟨other, mem, eq⟩ := Classical.not_not.mp tail
        exact ⟨other, Or.inr mem, eq⟩
    · rintro ⟨other, mem, eq⟩ denied
      rcases mem with same | mem
      · cases same
        exact denied.1 eq
      · exact denied.2 ⟨other, mem, eq⟩

end Solidity

/-- info: 'Solidity.holds_finiteMember' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.holds_finiteMember
