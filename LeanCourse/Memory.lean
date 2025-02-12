import Aesop
import Init.Core

set_option autoImplicit true

def IdT α β δ := α × List (β ⊕ δ)
def ValT α β γ δ := IdT α β δ ⊕ γ

open Sum

instance [DecidableEq α] [DecidableEq β] [DecidableEq δ] : DecidableEq (IdT α β δ) := by
  unfold IdT
  exact (inferInstanceAs _)

inductive Memory (α β γ δ : Type) where
  | mtm
  | write (mem : Memory α β γ δ) (id : IdT α β δ) (fld : β ⊕ δ) (val : ValT α β γ δ)
  | add   (mem : Memory α β γ δ) (id : α)


def read [DecidableEq α] [DecidableEq β] [DecidableEq δ] [Inhabited γ] (mem : Memory α β γ δ) (id : IdT α β δ) (fld : β ⊕ δ) : ValT α β γ δ :=
  match mem, id with
  | .mtm, _ => inr default
  | .write mem idM fldM val, _ => if idM = id && fldM = fld then val else read mem id fld
  | .add mem pId, (idd, ids) => if pId = idd
    then (match fld with
      | inl _ => inl ⟨idd, fld :: ids⟩
      | inr _ => inr default
      )
    else read mem id fld
