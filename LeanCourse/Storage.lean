import Aesop

import LeanCourse.Field

variable {ValTp IdTp ValSTp IdSTp : Type}

open Sum

inductive Value (ValTp ValSTp IdSTp : Type) where
  | mtst
  | var   (val : ValTp)
  | store (st : Value ValTp ValSTp IdSTp) (k : FieldSelector ValSTp IdSTp) (v : Value ValTp ValSTp IdSTp)

open Value

@[simp] def save [DecidableEq ValSTp] [DecidableEq IdSTp]
  (st : Value ValTp ValSTp IdSTp) (fields : List (FieldSelector ValSTp IdSTp))
  (v : Value ValTp ValSTp IdSTp) : Value ValTp ValSTp IdSTp :=
  match st, fields with
  | mtst, [] => v
  | mtst, k :: rest => store mtst k $ save mtst rest v
  | var _, _ => v
  | store _ _ _, [] => v
  | store st k v', xs@(k' :: ys) =>
    if k = k' then store st k (save v' ys v) else store (save st xs v) k v'

@[simp] theorem saveEmpty [DecidableEq ValSTp] [DecidableEq IdSTp]
  (st : Value ValTp ValSTp IdSTp) (v : Value ValTp ValSTp IdSTp) :
  save st [] v = v := by
  induction st <;> simp

@[simp] def select [DecidableEq ValSTp] [DecidableEq IdSTp] (st : Value ValTp ValSTp IdSTp)
  (k : FieldSelector ValSTp IdSTp) : Value ValTp ValSTp IdSTp :=
  match st with
  | mtst => mtst
  | var _ => mtst
  | store st k' v => if k' = k then v else select st k

@[simp] def find [DecidableEq ValSTp] [DecidableEq IdSTp] (st : Value ValTp ValSTp IdSTp)
  (flds : List $ FieldSelector ValSTp IdSTp) : Value ValTp ValSTp IdSTp :=
  match flds with
  | [] => st
  | x :: xs => find (select st x) xs

@[simp] def findOnEmpty [DecidableEq ValSTp] [DecidableEq IdSTp] (flds : List $ FieldSelector ValSTp IdSTp)
  : find mtst flds = (mtst : Value ValTp ValSTp IdSTp) := by
  induction flds <;> aesop

@[simp] def isStruct (st : Value ValTp ValSTp IdSTp) : Prop :=
  match st with
  | mtst => true
  | var _ => false
  | store st (.valS _) (var _) => isStruct st
  | store _  (.idS _) (var _) => false
  | store st (.idS _) st2 => And (isStruct st) (isStruct st2)
  | _ => false

@[simp] def Struct (ValTp ValSTp IdSTp : Type) : Type := { st : Value ValTp ValSTp IdSTp // isStruct st }

theorem structInside {st : Value ValTp ValSTp IdSTp} {k} {v} (wf : isStruct (store st k v)) : isStruct st := by
  cases v <;> aesop

theorem structInsideR {st : Value ValTp ValSTp IdSTp} {k} {v} (wf : isStruct (store st (.idS k) v))
  : isStruct v := by
  cases v <;> aesop

@[simp] theorem isStructSelect [DecidableEq ValSTp] [DecidableEq IdSTp] (st : Value ValTp ValSTp IdSTp)
  k (wf : isStruct st := by simp)
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

@[simp] theorem selectSave [DecidableEq ValSTp] [DecidableEq IdSTp]
  (st : Value ValTp ValSTp IdSTp) (k : FieldSelector ValSTp IdSTp) (path : List (FieldSelector ValSTp IdSTp))
  (v : Value ValTp ValSTp IdSTp) (k' : FieldSelector ValSTp IdSTp) (wf : isStruct st := by aesop) :
  select (save st (k :: path) v) k' =
  (if k = k' then save (select st k') path v else select st k') := by
  induction st with
  | mtst => simp
  | var => aesop
  | store st k''' _ ih =>
    have _ := ih $ structInside wf
    aesop
  done

@[simp] def pathInside (st : Value ValTp ValSTp IdSTp) (path : List $ FieldSelector ValSTp IdSTp) : Prop :=
  match path with
  | [] => true
  | p :: paths => match st with
    | mtst => false
    | var _ => false
    | store st k v => (p = k -> pathInside v paths) ∨ (p ≠ k -> pathInside st path)
