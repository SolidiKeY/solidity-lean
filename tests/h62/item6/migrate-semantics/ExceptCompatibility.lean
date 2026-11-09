/-!
Isolated constructor discrimination/injectivity fixtures for the migration.
These kernel-checked examples do not modify or validate AbiAccess itself.
-/
example {ε α : Type} (a : α) (e : ε)
    (h : (Except.ok a : Except ε α) = Except.error e) : False := by
  cases h

example {ε α : Type} (a : α) (e : ε)
    (h : (Except.error e : Except ε α) = Except.ok a) : False := by
  cases h

example {ε α : Type} (a b : α)
    (h : (Except.ok a : Except ε α) = Except.ok b) : a = b := by
  cases h
  rfl

example {ε α : Type} (a b : ε)
    (h : (Except.error a : Except ε α) = Except.error b) : a = b := by
  cases h
  rfl
