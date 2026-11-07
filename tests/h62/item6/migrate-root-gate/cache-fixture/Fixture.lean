namespace H62Cache

def witness : Nat := 62

theorem witness_exact : witness = 62 := rfl

theorem witness_not_reject_all : ∃ n : Nat, n = witness := ⟨62, rfl⟩

end H62Cache
