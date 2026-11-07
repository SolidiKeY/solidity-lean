/- Exact polymorphic original statement, constructor-disjointness proof. -/
namespace H62.BindCheck
theorem bind_check_eq_some {α β : Type} {o : Option α} {f : α → Bool} {v w : β}
    (h : (o >>= fun i => if f i = true then some v else none) = some w) : w = v := by
  cases o with
  | none => cases h
  | some i =>
    cases hf : f i
    · simp only [Option.bind_eq_bind, Option.bind_some, hf, Bool.false_eq_true, ↓reduceIte,
        reduceCtorEq] at h
    · simp only [Option.bind_eq_bind, Option.bind_some, hf, ↓reduceIte, Option.some.injEq] at h
      exact h.symm


#print axioms bind_check_eq_some
end H62.BindCheck
