namespace H62.DiscountRecursor
/-- Structural recursors keep unused lookup dictionary proofs out of gas. -/
def explicitLookup (table : List Nat) (index cap : Nat) : Nat :=
  List.casesOn table cap fun a tail =>
    Nat.casesOn index a fun i => explicitLookup tail i cap
/-- Every original table/index/fallback case is preserved. -/
theorem agrees (table : List Nat) (index cap : Nat) :
    explicitLookup table index cap = table.getD index cap := by
  induction table generalizing index with
  | nil => rfl
  | cons a table ih =>
    cases index with
    | zero => rfl
    | succ i => exact ih i
#print axioms explicitLookup
#print axioms agrees
end H62.DiscountRecursor
