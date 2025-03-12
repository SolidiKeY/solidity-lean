import Aesop

variable {α : Type}

theorem not_suff_imp_not_cons_suff (l1 l2 : List α) (x : α) :
  ¬ (l1 <:+ l2) → ¬ (x :: l1 <:+ l2) := by
  intro h1 h2
  apply h1
  apply List.IsSuffix.trans _ h2
  aesop
