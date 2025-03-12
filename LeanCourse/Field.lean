import Aesop

variable {ValType IdType ValSType IdSType : Type}

@[aesop safe [constructors, cases]]
inductive FieldSelector (ValSType IdSType : Type) where
  | valS  (valS : ValSType)
  | idS   (idS : IdSType)
  deriving DecidableEq

structure IdT (ValSType IdSType IdType : Type) where
  pId  : IdType
  flds : List (FieldSelector ValSType IdSType)

inductive ValT (ValType ValSType IdSType IdType : Type) where
  | val (val : ValType)
  | id  (id : IdT ValSType IdSType IdType)

instance [DecidableEq ValSType] [DecidableEq IdSType] [DecidableEq IdType] : DecidableEq (IdT ValSType IdSType IdType) := by
  rintro ⟨a1, b1⟩ ⟨a2, b2⟩
  simp
  have h : Decidable ((⟨a1, b1⟩ : IdType × List (FieldSelector ValSType IdSType)) = ⟨a2, b2⟩)  := by exact (inferInstanceAs _)
  cases h
  . apply isFalse; aesop
  . apply isTrue; aesop
