import Solidity.Calculus.FiniteMembership
import Solidity.Calculus.TermWk

/-!
# Membership in a finite literal domain filtered by a formula

The domain contains actual values at one primitive type. Only the guard
stands under the binder; the key is weakened from its original context.
An equality to the bound value requires the key's Theory denotation to be
`some v`. This is stronger than equality-membership between arbitrary
terms, where two halting terms can compare equal. The guard keeps the
existing KeY formula semantics: its equations do not require expressions
to return. This facility adds neither first-class sets nor Dafny's separate
expression-wellformedness checks, read frames or executable collections.
-/

namespace Solidity

variable {C : Contract} {Γ : Ctx} {p : PrimTy}

/-- Membership in literal values, using the existing typed equality fold. -/
def Fml.finiteValues (key : Tm C Γ (.val p)) (items : List p.Denote) : Fml C Γ :=
  .finiteMember key (items.map fun v => .app0 (.lit v))

/-- Literal membership cannot equate an undefined key with another failure. -/
theorem holds_finiteValues (σ : State C Γ) (key : Tm C Γ (.val p))
    (items : List p.Denote) :
    holds σ (Fml.finiteValues key items) ↔
      ∃ v, v ∈ items ∧ key.denote σ = some v := by
  rw [Fml.finiteValues, holds_finiteMember]
  constructor
  · rintro ⟨item, mem, eq⟩
    obtain ⟨v, value_mem, rfl⟩ := List.mem_map.mp mem
    exact ⟨v, value_mem, eq⟩
  · rintro ⟨v, mem, eq⟩
    exact ⟨.app0 (.lit v), List.mem_map.mpr ⟨v, mem, rfl⟩, eq⟩

/-- A genuine typed existential: outer key, finite literal domain, inner guard. -/
def Fml.filteredMember (x : Var) (key : Tm C Γ (.val p))
    (items : List p.Denote) (guard : Fml C (.val p :: Γ)) : Fml C Γ :=
  .not (.all x p (.not (.and (.eq (key.wk (.drop .refl)) (.pvV .here))
    (.and (.finiteValues (.pvV .here) items) guard))))

/-- Exact scoped denotation, including the key's definedness and outer scope. -/
theorem holds_filteredMember (σ : State C Γ) (x : Var) (key : Tm C Γ (.val p))
    (items : List p.Denote) (guard : Fml C (.val p :: Γ)) :
    holds σ (Fml.filteredMember x key items guard) ↔
      ∃ v, v ∈ items ∧ key.denote σ = some v ∧ holds (σ.push (t := .val p) v) guard := by
  classical
  change (¬ ∀ v : p.Denote, ¬ (_ ∧ _ ∧ _)) ↔ _
  rw [Classical.not_forall]
  simp only [Classical.not_not]
  have key_read (v : p.Denote) :
      (key.wk (.drop .refl)).denote (σ.push (t := .val p) v) = key.denote σ := by
    rw [Tm.denote_wk]
    rfl
  constructor
  · rintro ⟨v, eq, mem, guard⟩
    have eq' : key.denote σ = some v := by
      simpa only [holds, key_read, Tm.denote, TEnv.get] using eq
    obtain ⟨w, mem, same⟩ := (holds_finiteValues _ _ _).mp mem
    have same' : v = w := Option.some.inj same
    cases same'
    exact ⟨v, mem, eq', guard⟩
  · rintro ⟨v, mem, eq, guard⟩
    refine ⟨v, ?_, ?_, guard⟩
    · simpa only [holds, key_read, Tm.denote, TEnv.get] using eq
    · exact (holds_finiteValues _ _ _).mpr ⟨v, mem, rfl⟩

/-- Binder labels never change a scoped formula's meaning. -/
theorem holds_filteredMember_rename (σ : State C Γ) (x y : Var)
    (key : Tm C Γ (.val p)) (items : List p.Denote) (guard : Fml C (.val p :: Γ)) :
    holds σ (Fml.filteredMember x key items guard) ↔
      holds σ (Fml.filteredMember y key items guard) := by
  rw [holds_filteredMember, holds_filteredMember]

/-- Domain order and duplicate values affect no membership result. -/
theorem holds_filteredMember_domain (σ : State C Γ) (x : Var) (key : Tm C Γ (.val p))
    (as bs : List p.Denote) (guard : Fml C (.val p :: Γ))
    (same : ∀ v, v ∈ as ↔ v ∈ bs) :
    holds σ (Fml.filteredMember x key as guard) ↔
      holds σ (Fml.filteredMember x key bs guard) := by
  simp only [holds_filteredMember, same]

/-- An empty literal domain has no witness, independently of the guard. -/
theorem not_holds_filteredMember_nil (σ : State C Γ) (x : Var)
    (key : Tm C Γ (.val p)) (guard : Fml C (.val p :: Γ)) :
    ¬ holds σ (Fml.filteredMember x key [] guard) := by
  simp only [holds_filteredMember, List.not_mem_nil, false_and, exists_false, not_false_eq_true]

/-- A key with no Theory value cannot enter any filtered literal domain. -/
theorem not_holds_filteredMember_undefined (σ : State C Γ) (x : Var)
    (key : Tm C Γ (.val p)) (items : List p.Denote) (guard : Fml C (.val p :: Γ))
    (undefined : key.denote σ = none) :
    ¬ holds σ (Fml.filteredMember x key items guard) := by
  rw [holds_filteredMember]
  rintro ⟨v, _, eq, _⟩
  rw [undefined] at eq
  exact Option.noConfusion eq

end Solidity

/-- info: 'Solidity.holds_filteredMember' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.holds_filteredMember
