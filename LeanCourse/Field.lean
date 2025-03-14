import Aesop

variable {ValTp IdTp ValSTp IdSTp : Type}

@[aesop safe [constructors, cases]]
inductive FieldSelector (ValSTp IdSTp : Type) where
  | valS  (valS : ValSTp)
  | idS   (idS : IdSTp)
  deriving DecidableEq

structure IdT (ValSTp IdSTp IdTp : Type) where
  pId  : IdTp
  flds : List (FieldSelector ValSTp IdSTp)

inductive ValT (ValTp ValSTp IdSTp IdTp : Type) where
  | val (val : ValTp)
  | id  (id : IdT ValSTp IdSTp IdTp)

instance [DecidableEq ValSTp] [DecidableEq IdSTp] [DecidableEq IdTp] : DecidableEq (IdT ValSTp IdSTp IdTp) := by
  rintro ⟨a1, b1⟩ ⟨a2, b2⟩
  simp
  have h : Decidable ((⟨a1, b1⟩ : IdTp × List (FieldSelector ValSTp IdSTp)) = ⟨a2, b2⟩)  := by exact (inferInstanceAs _)
  cases h
  . apply isFalse; aesop
  . apply isTrue; aesop
