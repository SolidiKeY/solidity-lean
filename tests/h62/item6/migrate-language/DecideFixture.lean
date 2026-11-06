/-! Isolated migration controls: no project imports or trust shortcuts. -/
namespace H62.LanguageMigration
example (p q : Prop) [Decidable p] [Decidable q]
    (h : (decide p && decide q) = true) : p ∧ q := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

structure Bounds where
  signed : Bool
  bits : Nat
  valid : 8 ≤ bits

def Bounds.lower (t : Bounds) : Int := if t.signed then -2 ^ (t.bits - 1) else 0
def Bounds.upper (t : Bounds) : Int := if t.signed then 2 ^ (t.bits - 1) - 1 else 2 ^ t.bits - 1
def Bounds.inRange (t : Bounds) (v : Int) : Bool := decide (t.lower ≤ v) && decide (v ≤ t.upper)

example (t : Bounds) : t.inRange 0 = true := by
  have hp : (0 : Int) < 2 ^ (t.bits - 1) := Int.pow_pos (by decide)
  have hq : (0 : Int) < 2 ^ t.bits := Int.pow_pos (by decide)
  simp only [Bounds.inRange, Bool.and_eq_true, decide_eq_true_eq]
  unfold Bounds.lower Bounds.upper
  cases t.signed <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
end H62.LanguageMigration
