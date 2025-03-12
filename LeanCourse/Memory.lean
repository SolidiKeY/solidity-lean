import Aesop

set_option autoImplicit true
variable {IdType : Type}

@[aesop safe [constructors, cases]]
inductive FieldSelector (β γ : Type) where
  | valS  (valS : β)
  | idS (idS : γ)
  deriving DecidableEq

structure IdT (β γ IdType : Type) where
  pId  : IdType
  flds : List (FieldSelector β γ)

inductive ValT (α β γ IdType : Type) where
  | val (val : α)
  | id  (id : IdT β γ IdType)

instance [DecidableEq β] [DecidableEq γ] [DecidableEq IdType] : DecidableEq (IdT β γ IdType) := by
  rintro ⟨a1, b1⟩ ⟨a2, b2⟩
  simp
  have h : Decidable ((⟨a1, b1⟩ : IdType × List (FieldSelector β γ)) = ⟨a2, b2⟩)  := by exact (inferInstanceAs _)
  cases h
  . apply isFalse; aesop
  . apply isTrue; aesop

inductive Memory (α β γ IdType : Type) where
  | mtm
  | write (mem : Memory α β γ IdType) (id : IdT β γ IdType) (fld : FieldSelector β γ) (val : ValT α β γ IdType)
  | add   (mem : Memory α β γ IdType) (id : IdType)

namespace Memory

@[simp] def read [DecidableEq β] [DecidableEq γ] [DecidableEq IdType] [Inhabited α] (mem : Memory α β γ IdType) (id : IdT β γ IdType) (fld : FieldSelector β γ) : ValT α β γ IdType :=
  match mem, id with
  | .mtm, _ => .val default
  | .write mem idM fldM val, _ => if idM = id && fldM = fld then val else read mem id fld
  | .add mem pId, ⟨idd, valS⟩ => if pId = idd
    then (match fld with
      | .valS  _ => .val default
      | .idS _ => .id ⟨idd, fld :: valS⟩
      )
    else read mem id fld
