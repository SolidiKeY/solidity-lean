namespace H62.FinEquality
/-- An explicit computational equality, avoiding a changed inferred order package. -/
def explicitEq {p : Nat} (a b : Fin p) : Bool := Nat.beq a.val b.val
/-- The explicit comparison agrees with the current lawful Fin comparison for every input. -/
theorem agrees {p : Nat} (a b : Fin p) : explicitEq a b = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [explicitEq, Nat.beq_eq, beq_iff_eq, Fin.ext_iff]
#print axioms explicitEq
#print axioms agrees
end H62.FinEquality
