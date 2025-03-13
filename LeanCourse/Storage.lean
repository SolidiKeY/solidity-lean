import Aesop

import LeanCourse.Field

variable {ValType IdType ValSType IdSType : Type}

open Sum

inductive Value (ValType ValSType IdSType : Type) where
  | mtst
  | var   (val : ValType)
  | store (st : Value ValType ValSType IdSType) (k : FieldSelector ValSType IdSType) (v : Value ValType ValSType IdSType)

open Value

@[simp] def save [DecidableEq ValSType] [DecidableEq IdSType]
  (st : Value ValType ValSType IdSType) (fields : List (FieldSelector ValSType IdSType)) (v : Value ValType ValSType IdSType) : Value ValType ValSType IdSType :=
  match st, fields with
  | mtst, [] => v
  | mtst, k :: rest => store mtst k $ save mtst rest v
  | var _, _ => v
  | store _ _ _, [] => v
  | store st k v', xs@(k' :: ys) =>
    if k = k' then store st k (save v' ys v) else store (save st xs v) k v'

@[simp] theorem saveEmpty [DecidableEq ValSType] [DecidableEq IdSType]
  (st : Value ValType ValSType IdSType) (v : Value ValType ValSType IdSType) :
  save st [] v = v := by
  induction st <;> simp

@[simp] def select [DecidableEq ValSType] [DecidableEq IdSType] (st : Value ValType ValSType IdSType) (k : FieldSelector ValSType IdSType) : Value ValType ValSType IdSType :=
  match st with
  | mtst => mtst
  | var _ => mtst
  | store st k' v => if k' = k then v else select st k

@[simp] def isStruct (st : Value ValType ValSType IdSType) : Prop :=
  match st with
  | mtst => true
  | var _ => false
  | store st (.valS _) (var _) => isStruct st
  | store _  (.idS _) (var _) => false
  | store st (.idS _) st2 => And (isStruct st) (isStruct st2)
  | _ => false

theorem structInside {st : Value ValType ValSType IdSType} {k} {v} (wf : isStruct (store st k v)) : isStruct st := by
  cases v <;> aesop

theorem structInsideR {st : Value ValType ValSType IdSType} {k} {v} (wf : isStruct (store st (.idS k) v)) : isStruct v := by
  cases v <;> aesop

@[simp] theorem isStructSelect [DecidableEq ValSType] [DecidableEq IdSType] (st : Value ValType ValSType IdSType) k (wf : isStruct st := by simp)
  : isStruct (select st (.idS k)) :=
  match st, wf with
  | mtst, _ => by simp
  | var _, _ => by simp
  | store st (.valS _) (var _), wf => by
    apply isStructSelect st k _
    simp at wf
    assumption
  | store st (.idS id) (var c), wf => by simp at wf
  | store st (.idS id) mtst, wf => by
    simp at wf
    simp
    split
    simp
    apply isStructSelect
    assumption
  | store st (.idS id) (store _ _ _), wf => by
    simp at wf
    induction wf
    simp
    split
    assumption
    apply isStructSelect
    assumption

@[simp] theorem selectSave [DecidableEq ValSType] [DecidableEq IdSType]
  (st : Value ValType ValSType IdSType) (k : FieldSelector ValSType IdSType) (path : List (FieldSelector ValSType IdSType)) (v : Value ValType ValSType IdSType) (k' : FieldSelector ValSType IdSType) (wf : isStruct st := by aesop) :
  select (save st (k :: path) v) k' =
  (if k = k' then save (select st k') path v else select st k') := by
  induction st with
  | mtst => simp
  | var => aesop
  | store st k''' _ ih =>
    have _ := ih $ structInside wf
    aesop
  done
