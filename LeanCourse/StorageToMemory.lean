import LeanCourse.Memory
import LeanCourse.Storage

set_option autoImplicit true

open Sum
open Memory
open Value

@[simp] def copyStAux (mem : Memory α β γ δ) (id : IdT β γ δ) (st : Value α β γ) (wf : isStruct st) : Memory α β γ δ :=
  match st with
  | mtst => mem
  | var _ => by aesop
  | store st (inl k) .mtst => by aesop
  | store st (inl k) (var x) => write (copyStAux mem id st (by aesop)) id (inl k) (.inl x)
  | store st (inl k) (store a b c) => by aesop
  | store st x@(inr _) v =>
      let copyInt := copyStAux mem id st (by induction v <;> aesop)
      copyStAux copyInt ⟨id.1, x :: id.2⟩ v $ by
        induction v
        . aesop
        . simp at wf
        . simp at wf
          aesop

@[simp] def copySt (mem : Memory α β γ δ) (id : δ) (st : Value α β γ) (wf : isStruct st) : Memory α β γ δ :=
  copyStAux (add mem id) ⟨id, []⟩ st wf

def not_suff_imp_not_cons_suff (l1 l2 : List α) (x : α) :
  ¬ (l1 <:+ l2) → ¬ (x :: l1 <:+ l2) := by
  intro h1 h2
  apply h1
  apply List.IsSuffix.trans _ h2
  aesop


def readSkip [DecidableEq β] [DecidableEq γ] [DecidableEq δ] [Inhabited α]
  (mem : Memory α β γ δ) (pId pIdR : δ) (st : Value α β γ) (fxsL fxsR : List (β ⊕ γ)) (fld : β ⊕ γ)
  (wf : isStruct st) (pIdDiff : ¬pId = pIdR ⊕' pId = pIdR ×' ¬ fxsL <:+ (fld :: fxsR))
  : read (copyStAux mem ⟨pId, fxsL⟩ st wf) ⟨ pIdR , fxsR ⟩ fld = read mem ⟨ pIdR, fxsR⟩ fld :=

  match st with
  | mtst => by aesop
  | var _ => by simp at wf
  | store st (inl f) (var x) => by
    have h := readSkip mem pId pIdR st fxsL fxsR fld (by aesop) (by aesop)
    induction pIdDiff
    . unfold copyStAux
      simp
      rw [h]
      simp
      intros h2 h3
      cases h2
      aesop
      done
    . rename_i notSuff
      unfold copyStAux
      simp
      rw [h]
      simp
      intros h1 h2
      cases h1
      have h3 := List.suffix_cons fld fxsL
      have _ := notSuff.2 h3
      contradiction
  | store st (inr f) v => by
    have _ := structInside wf
    have stInR := structInsideR wf
    have _ := readSkip mem pId pIdR st fxsL fxsR fld (by aesop) (by aesop)
    have _ := not_suff_imp_not_cons_suff fxsL (fld :: fxsR) (inr f)
    let copyAuxVal := copyStAux mem ⟨pId, fxsL⟩ st (by aesop)
    have _ := readSkip copyAuxVal pId pIdR v (inr f :: fxsL) fxsR fld stInR
    aesop

inductive SameVal {α β γ δ : Type} : ValT α β γ δ → Value α β γ → Prop where
  | mk (v1 v2 : α) : SameVal (inl v1) (var v2)
  | mkEmpty (v1 : α) : SameVal (inl v1) mtst

open SameVal

def readFind [DecidableEq β] [DecidableEq γ] [DecidableEq δ] [Inhabited α]
  (mem : Memory α β γ δ) (id : δ) (st : Value α β γ) (fxs : List (β ⊕ γ)) (f : β) (wf : isStruct st)
  : SameVal (read (copySt mem id st wf) ⟨id, []⟩ (inl f)) (select st (inl f)) :=
  match st with
  | mtst => by
    simp
    constructor
  | var _ => by
    unfold isStruct at wf
    aesop
  | store st idS@(inr idSS) sv => by
    have copy := readSkip (copyStAux (add mem id) ⟨id, []⟩ st (structInside wf)) id id sv [.inr idSS] [] (inl f) (structInsideR wf)
      (.inr ⟨rfl, fun x => by
        have sub := List.IsSuffix.sublist x
        cases sub
        aesop
        ⟩)
    unfold copySt
    simp
    rw [copy]
    have readFindd := readFind mem id st [] f (structInside wf)
    apply readFindd
  | store st (inl idS) sv@(var _) => by
    have readFindd := readFind mem id st fxs f (structInside wf)
    simp
    split
    . constructor
    . apply readFindd
