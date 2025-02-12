import Aesop

set_option autoImplicit true

def IdT β γ δ := δ × List (β ⊕ γ)
def ValT α β γ δ := IdT β γ δ ⊕ α

open Sum

instance [DecidableEq β] [DecidableEq γ] [DecidableEq δ] : DecidableEq (IdT β γ δ) := by
  unfold IdT
  exact (inferInstanceAs _)

inductive Memory (α β γ δ : Type) where
  | mtm
  | write (mem : Memory α β γ δ) (id : IdT β γ δ) (fld : β ⊕ γ) (val : ValT α β γ δ)
  | add   (mem : Memory α β γ δ) (id : δ)

namespace Memory

@[simp] def read [DecidableEq β] [DecidableEq γ] [DecidableEq δ] [Inhabited α] (mem : Memory α β γ δ) (id : IdT β γ δ) (fld : β ⊕ γ) : ValT α β γ δ :=
  match mem, id with
  | .mtm, _ => inr default
  | .write mem idM fldM val, _ => if idM = id && fldM = fld then val else read mem id fld
  | .add mem pId, (idd, ids) => if pId = idd
    then (match fld with
      | inl _ => inl ⟨idd, fld :: ids⟩
      | inr _ => inr default
      )
    else read mem id fld
