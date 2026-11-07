namespace H62.DiscountLookup
/-- Bypass the unused panic-producing lookup dictionary field. -/
def explicitLookup (table : List Nat) (index cap : Nat) : Nat :=
  (List.get?Internal table index).getD cap
/-- This is definitional equality, for every table, index and fallback. -/
theorem agrees (table : List Nat) (index cap : Nat) :
    explicitLookup table index cap = table.getD index cap := rfl
#print axioms explicitLookup
#print axioms agrees
end H62.DiscountLookup
