import Aesop

import LeanCourse.Memory

set_option autoImplicit true

open Sum

inductive Value (α β γ : Type) where
  | mtst
  | var   (val : α)
  | store (st : Value α β γ) (k : FieldSelector β γ) (v : Value α β γ)

open Value

@[simp] def save [DecidableEq β] [DecidableEq γ]
  (st : Value α β γ) (fields : List (FieldSelector β γ)) (v : Value α β γ) : Value α β γ :=
  match st, fields with
  | mtst, [] => v
  | mtst, k :: rest => store mtst k $ save mtst rest v
  | var _, _ => v
  | store st k _, [] => store st k v
  | store st k v', xs@(k' :: ys) =>
    if k = k' then store st k (save v' ys v) else store (save st xs v) k v'

@[simp] def select [DecidableEq β] [DecidableEq γ] (st : Value α β γ) (k : FieldSelector β γ) : Value α β γ :=
  match st with
  | mtst => mtst
  | var _ => mtst
  | store st k' v => if k' = k then v else select st k

@[simp] def isStruct (st : Value α β γ) : Prop :=
  match st with
  | mtst => true
  | var _ => false
  | store st (.valS _) (var _) => isStruct st
  | store _  (.idS _) (var _) => false
  | store st (.idS _) st2 => And (isStruct st) (isStruct st2)
  | _ => false

theorem structInside {st : Value α β γ} {k} {v} (wf : isStruct (store st k v)) : isStruct st := by
  cases v <;> aesop

theorem structInsideR {st : Value α β γ} {k} {v} (wf : isStruct (store st (.idS k) v)) : isStruct v := by
  cases v <;> aesop

theorem selectSave [DecidableEq β] [DecidableEq γ]
  (st : Value α β γ) (k : FieldSelector β γ) (path : List (FieldSelector β γ)) (v : Value α β γ) (k' : FieldSelector β γ) (wf : isStruct st := by simp) :
  select (save st (k :: path) v) k' =
  (if k = k' then save (select st k') path v else select st k') := by
  induction st with
  | mtst => simp
  | var => aesop
  | store st k''' _ ih =>
    have _ := ih $ structInside wf
    aesop
  done
