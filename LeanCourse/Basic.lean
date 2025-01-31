set_option autoImplicit true

open Sum

inductive Value (α β γ : Type) where
  | mtst : Value α β γ
  | var (val : α) : Value α β γ
  | store (st : Value α β γ) (k : β ⊕ γ) (v : Value α β γ) : Value α β γ

open Value

def save [DecidableEq β] [DecidableEq γ]
  (st : Value α β γ) (fields : List (β ⊕ γ)) (v : Value α β γ) : Value α β γ :=
  match st, fields with
  | mtst, [] => v
  | mtst, k :: rest => store mtst k $ save mtst rest v
  | var _, _ => v
  | store st k _, [] => store st k v
  | store st k v', xs@(k' :: ys) =>
    if k = k' then store st k (save v' ys v) else store (save st xs v) k v'

def select [DecidableEq β] [DecidableEq γ] (st : Value α β γ) (k : β ⊕ γ) : Value α β γ :=
  match st with
  | mtst => mtst
  | var _ => mtst
  | store st k' v => if k = k' then v else select st k'

theorem selectSave [DecidableEq β] [DecidableEq γ]
  (st : Value α β γ) (k : β ⊕ γ) (path : List (β ⊕ γ)) (v : Value α β γ) (k' : β ⊕ γ) :
  select (save st (k :: path) v) k' =
  (if k = k' then save (select st k') path v else select st k') := by
  induction st
  . let b := if k' = k then save mtst path v else select mtst k
    have h : select (save mtst (k :: path) v) k' = b := by
      unfold save select b
      rfl
    rw [h]
    unfold b
    sorry
  . sorry
  . sorry
  done
