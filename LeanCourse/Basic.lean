set_option autoImplicit true

open Sum

inductive Struct (α β γ : Type) where
  | mtst : Struct α β γ
  | var (val : α) : Struct α β γ
  | store (st : Struct α β γ) (k : β ⊕ γ) (v : Struct α β γ) : Struct α β γ

open Struct

def save [DecidableEq β] [DecidableEq γ]
  (st : Struct α β γ) (fields : List (β ⊕ γ)) (v : Struct α β γ) : Struct α β γ :=
  match st, fields with
  | mtst, [] => v
  | mtst, k :: rest => store mtst k $ save mtst rest v
  | var val, xs => sorry
  | store st k v, [] => store st k v
  | store st k v', xs@(k' :: _) =>
    if k = k' then store st k sorry else store (save st xs v) k sorry

def select [DecidableEq β] [DecidableEq γ] (st : Struct α β γ) (k : β ⊕ γ) : Struct α β γ :=
  match st with
  | mtst => mtst
  | var val => sorry
  | store st k' v => if k = k' then v else select st k'

theorem selectSave [DecidableEq β] [DecidableEq γ]
  (st : Struct α β γ) (k : β ⊕ γ) (path : List (β ⊕ γ)) (v : Struct α β γ) (k' : β ⊕ γ) :
  select (save st (k :: path) v) k' =
  (if k = k' then save (select st k') path v else select st k') := by
  sorry
