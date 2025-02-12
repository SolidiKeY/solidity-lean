import LeanCourse.Memory
import LeanCourse.Storage

set_option autoImplicit true

open Sum
open Memory
open Value

def copyStAux (mem : Memory α β γ δ) (id : IdT β γ δ) (st : Value α β γ) (wf : isStruct st) : Memory α β γ δ :=
  match st with
  | mtst => mem
  | var _ => by aesop
  | store st (inl k) .mtst => by aesop
  | store st (inl k) (var x) => write (copyStAux mem id st (by aesop)) id (by aesop) (inr x)
  | store st (inl k) (store a b c) => by aesop
  | store st x@(inr _) v =>
      let copyInt := copyStAux mem id st (by induction v <;> aesop)
      copyStAux copyInt ⟨id.1, x :: id.2⟩ v $ by
        induction v
        . aesop
        . simp at wf
        . simp at wf
          aesop

def copySt (mem : Memory α β γ δ) (id : δ) (st : Value α β γ) (wf : isStruct st) : Memory α β γ δ :=
  copyStAux (add mem id) ⟨id, []⟩ st wf

def readSkip [DecidableEq β] [DecidableEq γ] [DecidableEq δ] [Inhabited α]
  (mem : Memory α β γ δ) (pId : δ) (pIdR : δ) (st : Value α β γ) (fxs : List (β ⊕ γ)) (f : β)
  (wf : isStruct st) (pIdDiff : ¬pId = pIdR ⊕' pId = pIdR ×' ¬ List.IsSuffix fxsL (fld :: fxsR))
  : read (copyStAux mem ⟨pId, fxsL⟩ st wf) ⟨ pIdR , fxsR ⟩ fld = read mem ⟨ pIdR, fxsR⟩ fld :=

  match st with
  | mtst => sorry
  | var _ => sorry
  | store st f v => sorry
