import LeanCourse.Memory
import LeanCourse.Storage

set_option autoImplicit true

open Sum
open Memory
open Value

def copyStAux (mem : Memory α β γ δ) (id : IdT β γ δ) (st : Value α β γ) (wf : isStruct st) : Memory α β γ δ :=
  match st, wf with
  | mtst, _ => mem
  | var _, _ => by aesop
  | .store st (.inl k) .mtst, _ => by aesop
  | .store st (.inl k) (.var x), _ => write (copyStAux mem id st (by aesop)) id (by aesop) (inr x)
  | .store st (.inl k) (.store a b c), _ => sorry

  -- | .store st (.inl k) v, _ => write (copyStAux mem id st _) id _ (inr _)
  | store st (inr k) v, _ => sorry
  -- | store st _ _, _ => sorry
