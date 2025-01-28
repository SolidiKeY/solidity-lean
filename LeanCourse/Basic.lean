set_option autoImplicit true

open Sum

inductive Struct (α β γ : Type) where
  | mtst : Struct α β γ
  | var : Struct α β γ
  | store (st : Struct α β γ) (k : β ⊕ γ) (v : Struct α β γ) : Struct α β γ

open Struct

def save (st : Struct α β γ) (fields : List (β ⊕ γ)) (v : α ⊕ Struct α β γ) : Struct α β γ :=
  match st, fields with
  | mtst, [] => sorry
  | mtst, k :: rest => store mtst k $ save mtst rest v
  | store st k v, [] => store st k v
  | store st k (inr v'), xs@(k' :: _) =>
    if k = k' then store st k (inr v') else store (save st xs v) k (inr v')
  | store st k (inl v'), xs@(k' :: rest) =>
    if k = k' then store st k (inl $ save v' rest v) else store (save st xs v) k (inl v')

def select (st : Struct α β γ) (k : Nat) : Struct α β γ :=
  match st with
  | mtst => mtst
  | store st k' v => if k = k' then v else select st k'

theorem selectSave (st : Struct α β γ) (k : Nat) (path : List Nat) (v : Struct α β γ) (k' : Nat) :
  select (save st (k :: path) v) k' =
  (if k = k' then save (select st k') path v else select st k') := by
  sorry
