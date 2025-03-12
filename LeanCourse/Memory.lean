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

inductive Memory (ValType ValSType IdSType IdType : Type) where
  | mtm
  | write (mem : Memory ValType ValSType IdSType IdType) (id : IdT ValSType IdSType IdType) (fld : FieldSelector ValSType IdSType) (val : ValT ValType ValSType IdSType IdType)
  | add   (mem : Memory ValType ValSType IdSType IdType) (id : IdType)

namespace Memory

@[simp] def read [DecidableEq ValSType] [DecidableEq IdSType] [DecidableEq IdType] [Inhabited ValType] (mem : Memory ValType ValSType IdSType IdType) (id : IdT ValSType IdSType IdType) (fld : FieldSelector ValSType IdSType) : ValT ValType ValSType IdSType IdType :=
  match mem, id with
  | .mtm, _ => .val default
  | .write mem idM fldM val, _ => if idM = id && fldM = fld then val else read mem id fld
  | .add mem pId, ⟨idd, valS⟩ => if pId = idd
    then (match fld with
      | .valS  _ => .val default
      | .idS _ => .id ⟨idd, fld :: valS⟩
      )
    else read mem id fld
