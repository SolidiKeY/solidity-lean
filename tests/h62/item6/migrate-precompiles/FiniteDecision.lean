namespace H62.FiniteDecision
def explicitEq {p : Nat} (a b : Fin p) : Bool := decide (a = b)
theorem agrees {p : Nat} (a b : Fin p) : explicitEq a b = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [explicitEq, decide_eq_true_eq, beq_iff_eq]
#print axioms explicitEq
#print axioms agrees
end H62.FiniteDecision
