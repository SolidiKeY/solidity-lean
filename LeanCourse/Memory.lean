import Aesop

set_option autoImplicit true

structure IdT (β γ δ : Type) where
  pId  : δ
  flds : List (β ⊕ γ)

def ValT α β γ δ := α ⊕ IdT β γ δ

open Sum

instance [DecidableEq β] [DecidableEq γ] [DecidableEq δ] : DecidableEq (IdT β γ δ) := by
  rintro ⟨a1, b1⟩ ⟨a2, b2⟩
  simp
  have h : Decidable ((⟨a1, b1⟩ : δ × List (β ⊕ γ)) = ⟨a2, b2⟩)  := by exact (inferInstanceAs _)
  cases h
  . apply isFalse; aesop
  . apply isTrue; aesop

inductive Memory (α β γ δ : Type) where
  | mtm
  | write (mem : Memory α β γ δ) (id : IdT β γ δ) (fld : β ⊕ γ) (val : ValT α β γ δ)
  | add   (mem : Memory α β γ δ) (id : δ)

namespace Memory

@[simp] def read [DecidableEq β] [DecidableEq γ] [DecidableEq δ] [Inhabited α] (mem : Memory α β γ δ) (id : IdT β γ δ) (fld : β ⊕ γ) : ValT α β γ δ :=
  match mem, id with
  | .mtm, _ => inl default
  | .write mem idM fldM val, _ => if idM = id && fldM = fld then val else read mem id fld
  | .add mem pId, ⟨idd, ids⟩ => if pId = idd
    then (match fld with
      | inl _ => inl default
      | inr _ => inr ⟨idd, fld :: ids⟩
      )
    else read mem id fld
