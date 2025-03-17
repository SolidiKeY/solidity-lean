import LeanCourse.Memory
import LeanCourse.Storage
import LeanCourse.Lib

variable {ValTp IdTp ValSTp IdSTp : Type}

open Sum
open Memory
open Value

structure State (ValTp ValSTp IdSTp IdTp : Type) where
  memory  : Memory ValTp ValSTp IdSTp IdTp
  storage : Value ValTp ValSTp IdSTp

@[simp] def copyStAux (mem : Memory ValTp ValSTp IdSTp IdTp) (id : IdT ValSTp IdSTp IdTp)
  (st : Value ValTp ValSTp IdSTp) (wf : isStruct st := by simp) : Memory ValTp ValSTp IdSTp IdTp :=
  match st with
  | mtst => mem
  | var _ => by aesop
  | store st (.valS k) .mtst => by aesop
  | store st (.valS k) (var x) => write (copyStAux mem id st (by aesop)) id (.valS k) (.val x)
  | store st (.valS k) (store a b c) => by aesop
  | store st x@(.idS _) v =>
      let copyInt := copyStAux mem id st (by induction v <;> aesop)
      copyStAux copyInt ⟨id.1, x :: id.2⟩ v $ by
        induction v
        . aesop
        . simp at wf
        . simp at wf
          aesop

@[simp] def copySt (mem : Memory ValTp ValSTp IdSTp IdTp) (id : IdTp) (st : Value ValTp ValSTp IdSTp)
  (wf : isStruct st := by simp) : Memory ValTp ValSTp IdSTp IdTp :=
  copyStAux (add mem id) ⟨id, []⟩ st wf

@[simp] theorem readSkipAux [DecidableEq ValSTp] [DecidableEq IdSTp] [DecidableEq IdTp] [Inhabited ValTp]
  (mem : Memory ValTp ValSTp IdSTp IdTp) (pId pIdR : IdTp) (st : Value ValTp ValSTp IdSTp)
  (fxsL fxsR : List (FieldSelector ValSTp IdSTp)) (fld : FieldSelector ValSTp IdSTp)
  (wf : isStruct st := by simp) (pIdDiff : not (pId = pIdR) ∨ pId = pIdR ∧ not (fxsL <:+ fld :: fxsR) := by aesop)
  : read (copyStAux mem ⟨pId, fxsL⟩ st wf) ⟨ pIdR , fxsR ⟩ fld = read mem ⟨ pIdR, fxsR⟩ fld :=

  match st with
  | mtst => by aesop
  | var _ => by simp at wf
  | store st (.valS f) (var x) => by
    have h := readSkipAux mem pId pIdR st fxsL fxsR fld (by aesop) (by aesop)
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
      induction h2
      cases h1
      have h3 := List.suffix_cons fld fxsL
      rcases notSuff with ⟨_, nDec⟩
      simp at nDec
  | store st (.idS f) v => by
    have _ := structInside wf
    have stInR := structInsideR wf
    have _ := readSkipAux mem pId pIdR st fxsL fxsR fld (by aesop) (by aesop)
    have _ := not_suff_imp_not_cons_suff fxsL (fld :: fxsR) (.idS f)
    let copyAuxVal := copyStAux mem ⟨pId, fxsL⟩ st (by aesop)
    have _ := readSkipAux copyAuxVal pId pIdR v (.idS f :: fxsL) fxsR fld stInR
    aesop

@[simp] theorem readSkip [DecidableEq ValSTp] [DecidableEq IdSTp] [DecidableEq IdTp] [Inhabited ValTp]
  (mem : Memory ValTp ValSTp IdSTp IdTp) (pId pIdR : IdTp) (st : Value ValTp ValSTp IdSTp)
  (fxsR : List (FieldSelector ValSTp IdSTp)) (fld : FieldSelector ValSTp IdSTp)
  (wf : isStruct st := by aesop) (pIdDiff : not (pId = pIdR) := by aesop)
  : read (copySt mem pId st wf) ⟨ pIdR , fxsR ⟩ fld = read mem ⟨ pIdR, fxsR⟩ fld := by aesop

inductive SameVal {ValTp ValSTp IdSTp IdTp : Type} [Inhabited ValTp]
  : ValT ValTp ValSTp IdSTp IdTp → Value ValTp ValSTp IdSTp → Prop where
  | mk (v : ValTp) : SameVal (.val v) (.var v)
  | mkEmpty : SameVal (.val default) mtst

open SameVal

theorem readFind [DecidableEq ValSTp] [DecidableEq IdSTp] [DecidableEq IdTp] [Inhabited ValTp]
  (mem : Memory ValTp ValSTp IdSTp IdTp) (id : IdTp) (st : Value ValTp ValSTp IdSTp)
  (fxs : List (FieldSelector ValSTp IdSTp)) (f : ValSTp) (wf : isStruct st := by simp)
  : SameVal (read (copySt mem id st wf) ⟨id, []⟩ (.valS f)) (select st (.valS f)) :=
  match st with
  | mtst => by
    simp
    constructor
  | var _ => by
    unfold isStruct at wf
    aesop
  | store st valS@(.idS valSS) sv => by
    have copy := readSkipAux (copyStAux (add mem id) ⟨id, []⟩ st (structInside wf)) id id sv
      [.idS valSS] [] (.valS f) (structInsideR wf) $ by
      simp
      intro h
      cases List.IsSuffix.sublist h
      aesop
    unfold copySt
    simp
    rw [copy]
    have readFindd := readFind mem id st [] f (structInside wf)
    apply readFindd
  | store st (.valS valS) sv@(var _) => by
    have readFindd := readFind mem id st fxs f (structInside wf)
    simp
    split
    . constructor
    . apply readFindd

@[simp] theorem skipIdRead [DecidableEq ValSTp] [DecidableEq IdSTp] [DecidableEq IdTp] [Inhabited ValTp]
  (mem : Memory ValTp ValSTp IdSTp IdTp) (idC idR : IdT ValSTp IdSTp IdTp) (st : Value ValTp ValSTp IdSTp)
  (fld : IdSTp) (wf : isStruct st := by simp)
  : read (copyStAux mem idC st wf) idR (.idS fld) = read mem idR (.idS fld) :=
  match st with
  | mtst => by aesop
  | var _ => by
    unfold isStruct at wf
    aesop
  | store st (.valS f) (var _) => by
    have _ := skipIdRead mem idC idR st fld (structInside wf)
    aesop
  | store st (.idS id) v => by
    have wfIn := structInside wf
    have _ := skipIdRead mem idC idR st fld wfIn
    have _ := skipIdRead (copyStAux mem idC st wfIn) ⟨idC.1, .idS id :: idC.2⟩ idR v fld (structInsideR wf)
    aesop

@[simp] theorem readGetId [DecidableEq ValSTp] [DecidableEq IdSTp] [DecidableEq IdTp] [Inhabited ValTp]
  (mem : Memory ValTp ValSTp IdSTp IdTp) (pId : IdTp) (st : Value ValTp ValSTp IdSTp)
  (fxs : List (FieldSelector ValSTp IdSTp))
  (fld : IdSTp) (wf : isStruct st := by simp)
  : read (copySt mem pId st wf) ⟨pId, fxs⟩ (.idS fld) = .id ⟨pId, .idS fld :: fxs⟩ := by
  have h := skipIdRead (add mem pId) ⟨pId, []⟩ ⟨pId, fxs⟩ st fld wf
  unfold copySt
  rw [h]
  simp
