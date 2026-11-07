import Lean

/-! Isolated migration fixtures. No production import, source edits, premise
changes, or trust shortcuts. Near/Covers are exact local copies of the two
predicates at the blocked dependency boundary, for owner-reviewable diagnosis.
These fixtures do not prove the external module or the storage migration. -/
namespace StorageMigrationFixture

theorem contains_split (x : Nat) (t : List Nat) :
    (fun a => (x :: t).contains a) = fun a => a == x || t.contains a := by
  funext a
  exact List.contains_cons

def Near (N L a b : Nat) : Prop :=
  (a < b + L ∧ b < a + L) ∨ a + N < b + L ∨ b + N < a + L

def Covers (N L a r : Nat) : Prop :=
  (a ≤ r ∧ r < a + L) ∨ r + N < a + L

instance {N L a b : Nat} : Decidable (Near N L a b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))
instance {N L a r : Nat} : Decidable (Covers N L a r) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem near_interval (N L a b : Nat) (hb : b < N) (ha : a < N)
    (hn : decide (Near N L a b) = true) :
    decide (b + 1 - L ≤ a ∧ a < b + L) ||
      decide (0 ≤ a ∧ a < b + L - N) ||
      decide (b + N + 1 - L ≤ a ∧ a < N) = true := by
  have hn' : Near N L a b := of_decide_eq_true hn
  simp only [Near] at hn'
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem covers_interval (N L a r : Nat) (_hr : r < N) (ha : a < N)
    (hn : decide (Covers N L a r) = true) :
    decide (r + 1 - L ≤ a ∧ a < r + 1) ||
      decide (r + N + 1 - L ≤ a ∧ a < N) = true := by
  have hn' : Covers N L a r := of_decide_eq_true hn
  simp only [Covers] at hn'
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  omega

example : ¬ Near 100 1 0 50 := by decide
example : ¬ Covers 100 1 0 50 := by decide
end StorageMigrationFixture

#print axioms StorageMigrationFixture.contains_split
#print axioms StorageMigrationFixture.near_interval
#print axioms StorageMigrationFixture.covers_interval
