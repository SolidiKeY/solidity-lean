import Solidity.Frontend.StatementGrammarH28.ControlFreePr

/-! H31 proof-only all-atom continuation keyword absence. Existing syntax,
precedence contracts, expression-uniqueness exclusion and budgets unchanged. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem controlFree_elem_atom (e : Elem) : ControlFree [.elem e] :=
  .token _ rfl

theorem controlFree_elem (e : Elem) : ControlFree e.toks := by
  cases e <;> first
    | exact controlFree_elem_atom _
    | exact .append (controlFree_elem_atom _) (controlFree_kw _ (by decide))

theorem controlFree_path (p : IdPath) : ControlFree p.toks := by
  have tail : ∀ ss : List String,
      ControlFree (ss.flatMap (fun s => [.punct .period, .ident s])) := by
    intro ss
    induction ss with
    | nil => exact .empty
    | cons s ss ih =>
      exact .append (.append
        (controlFree_punct .period)
        (controlFree_id s)) ih
  exact .append (controlFree_id p.head) (tail p.tail)

theorem controlFree_visibility (v : Visibility) : ControlFree v.toks := by
  cases v <;> exact controlFree_kw _ (by decide)

theorem controlFree_mutability (v : Mutability) : ControlFree v.toks := by
  cases v <;> exact controlFree_kw _ (by decide)

theorem controlFree_dataLoc (v : DataLoc) : ControlFree v.toks := by
  cases v <;> exact controlFree_kw _ (by decide)

theorem litP_controlFree (l : Lit) : PrEnsures (litP l) ControlFree := by
  cases l with
  | str b => exact fragsP_controlFree _ _ (fun _ => .token _ rfl)
  | hexStr b => exact fragsP_controlFree _ _ (fun _ => .token _ rfl)
  | unicodeStr b => exact fragsP_controlFree _ _ (fun _ => .token _ rfl)
  | bool b => exact ensures_pure _ _ (.token _ rfl)
  | num n => exact ensures_pure _ _ (.token _ rfl)

theorem controlFree_prefix (op : PrefixOp) : ControlFree (op.punct) := by
  cases op <;> first
    | exact controlFree_kw _ (by decide)
    | exact controlFree_punct _

theorem controlFree_suffix (op : SuffixOp) : ControlFree (pu op.punct) := by
  cases op <;> first
    | exact controlFree_kw _ (by decide)
    | exact controlFree_punct _

theorem controlFree_mul (op : MulOp) : ControlFree (pu op.punct) := by
  cases op <;> first
    | exact controlFree_kw _ (by decide)
    | exact controlFree_punct _

theorem controlFree_add (op : AddOp) : ControlFree (pu op.punct) := by
  cases op <;> first
    | exact controlFree_kw _ (by decide)
    | exact controlFree_punct _

theorem controlFree_shift (op : ShiftOp) : ControlFree (pu op.punct) := by
  cases op <;> first
    | exact controlFree_kw _ (by decide)
    | exact controlFree_punct _

theorem controlFree_order (op : OrderOp) : ControlFree (pu op.punct) := by
  cases op <;> first
    | exact controlFree_kw _ (by decide)
    | exact controlFree_punct _

theorem controlFree_equality (op : EqOp) : ControlFree (pu op.punct) := by
  cases op <;> first
    | exact controlFree_kw _ (by decide)
    | exact controlFree_punct _

theorem controlFree_assign (op : AssignOp) : ControlFree (pu op.punct) := by
  cases op <;> first
    | exact controlFree_kw _ (by decide)
    | exact controlFree_punct _

theorem controlFree_single (slot : Slot) (ts : List Tok) (h : ControlFree ts) :
    ∀ pair ∈ single slot ts, ControlFree pair.2 := by
  unfold single
  split
  · intro pair hp; cases hp
  · intro pair hp
    have he : pair = (slot, ts) := List.mem_singleton.mp hp
    subst pair
    exact h

theorem arrange_empty_mods_controlFree (o : List Slot) :
    ∀ singles out, (∀ pair ∈ singles, ControlFree pair.2) →
      arrange o singles [] = some out → ControlFree out := by
  induction o with
  | nil =>
    intro singles out hs he
    cases singles with
    | nil => cases he; exact .empty
    | cons pair rest => cases he
  | cons slot order ih =>
    intro singles out hs he
    simp only [arrange] at he
    split at he
    · cases he
    · cases hf : singles.find? (fun pair => pair.1 == slot) with
      | none => rw [hf] at he; cases he
      | some pair =>
        rw [hf] at he
        obtain ⟨rest, hr, eq⟩ := Option.map_eq_some_iff.mp he
        have pairIn : pair ∈ singles := List.mem_of_find?_eq_some hf
        have tail : ControlFree rest := ih _ rest
          (fun p hp => hs p (List.mem_filter.mp hp).1) hr
        subst out
        exact .append (hs pair pairIn) tail

theorem attrsP_empty_mods_controlFree (singles : List (Slot × List Tok))
    (hs : ∀ pair ∈ singles, ControlFree pair.2) (o : List Slot) :
    PrEnsures (attrsP singles [] o) ControlFree := by
  intro L ts M he
  change (arrange o singles []).map (fun a => (a, L)) = some (ts, M) at he
  obtain ⟨a, ha, eq⟩ := Option.map_eq_some_iff.mp he
  have words : a = ts := congrArg Prod.fst eq
  subst ts
  exact arrange_empty_mods_controlFree o singles a hs ha

end Solidity.Frontend.StatementGrammarH28
