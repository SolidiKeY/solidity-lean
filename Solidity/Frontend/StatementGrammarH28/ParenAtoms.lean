import Solidity.Frontend.StatementGrammarH28.ParenPr

/-! Immutable atom combinators preserve parenthesis balance. Payload bytes
remain atoms; no expression uniqueness or producer changes are used. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem parenBalanced_elem_atom (e : Elem) : ParenBalanced [.elem e] :=
  .token _ (by intro h; cases h) (by intro h; cases h)

theorem parenBalanced_elem (e : Elem) : ParenBalanced e.toks := by
  cases e <;> first
    | exact parenBalanced_elem_atom _
    | exact .append (parenBalanced_elem_atom _) (parenBalanced_kw _)

theorem parenBalanced_path (p : IdPath) : ParenBalanced p.toks := by
  have tail : ∀ ss : List String,
      ParenBalanced (ss.flatMap (fun s => [.punct .period, .ident s])) := by
    intro ss
    induction ss with
    | nil => exact .empty
    | cons s ss ih =>
      exact .append (.append
        (parenBalanced_punct .period (by intro h; cases h) (by intro h; cases h))
        (parenBalanced_id s)) ih
  exact .append (parenBalanced_id p.head) (tail p.tail)

theorem parenBalanced_visibility (v : Visibility) : ParenBalanced v.toks := by
  cases v <;> exact parenBalanced_kw _

theorem parenBalanced_mutability (v : Mutability) : ParenBalanced v.toks := by
  cases v <;> exact parenBalanced_kw _

theorem parenBalanced_dataLoc (v : DataLoc) : ParenBalanced v.toks := by
  cases v <;> exact parenBalanced_kw _

theorem parenBalanced_yulLit (l : YulLit) : ParenBalanced l.toks := by
  cases l <;> exact .token _ (by intro h; cases h) (by intro h; cases h)

theorem litP_parenBalanced (l : Lit) : PrEnsures (litP l) ParenBalanced := by
  cases l with
  | str b => exact fragsP_parenBalanced _ _ (fun _ => .token _ (by intro h; cases h) (by intro h; cases h))
  | hexStr b => exact fragsP_parenBalanced _ _ (fun _ => .token _ (by intro h; cases h) (by intro h; cases h))
  | unicodeStr b => exact fragsP_parenBalanced _ _ (fun _ => .token _ (by intro h; cases h) (by intro h; cases h))
  | bool b => exact ensures_pure _ _ (.token _ (by intro h; cases h) (by intro h; cases h))
  | num n => exact ensures_pure _ _ (.token _ (by intro h; cases h) (by intro h; cases h))

theorem parenBalanced_prefix (op : PrefixOp) : ParenBalanced (op.punct) := by
  cases op <;> first
    | exact parenBalanced_kw _
    | exact parenBalanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem parenBalanced_suffix (op : SuffixOp) : ParenBalanced (pu op.punct) := by
  cases op <;> first
    | exact parenBalanced_kw _
    | exact parenBalanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem parenBalanced_mul (op : MulOp) : ParenBalanced (pu op.punct) := by
  cases op <;> first
    | exact parenBalanced_kw _
    | exact parenBalanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem parenBalanced_add (op : AddOp) : ParenBalanced (pu op.punct) := by
  cases op <;> first
    | exact parenBalanced_kw _
    | exact parenBalanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem parenBalanced_shift (op : ShiftOp) : ParenBalanced (pu op.punct) := by
  cases op <;> first
    | exact parenBalanced_kw _
    | exact parenBalanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem parenBalanced_order (op : OrderOp) : ParenBalanced (pu op.punct) := by
  cases op <;> first
    | exact parenBalanced_kw _
    | exact parenBalanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem parenBalanced_equality (op : EqOp) : ParenBalanced (pu op.punct) := by
  cases op <;> first
    | exact parenBalanced_kw _
    | exact parenBalanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem parenBalanced_assign (op : AssignOp) : ParenBalanced (pu op.punct) := by
  cases op <;> first
    | exact parenBalanced_kw _
    | exact parenBalanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem parenBalanced_single (slot : Slot) (ts : List Tok) (h : ParenBalanced ts) :
    ∀ pair ∈ single slot ts, ParenBalanced pair.2 := by
  unfold single
  split
  · intro pair hp; cases hp
  · intro pair hp
    have he : pair = (slot, ts) := List.mem_singleton.mp hp
    subst pair
    exact h

theorem arrange_empty_mods_parenBalanced (o : List Slot) :
    ∀ singles out, (∀ pair ∈ singles, ParenBalanced pair.2) →
      arrange o singles [] = some out → ParenBalanced out := by
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
        have tail : ParenBalanced rest := ih _ rest
          (fun p hp => hs p (List.mem_filter.mp hp).1) hr
        subst out
        exact .append (hs pair pairIn) tail

theorem attrsP_empty_mods_parenBalanced (singles : List (Slot × List Tok))
    (hs : ∀ pair ∈ singles, ParenBalanced pair.2) (o : List Slot) :
    PrEnsures (attrsP singles [] o) ParenBalanced := by
  intro L ts M he
  change (arrange o singles []).map (fun a => (a, L)) = some (ts, M) at he
  obtain ⟨a, ha, eq⟩ := Option.map_eq_some_iff.mp he
  have words : a = ts := congrArg Prod.fst eq
  subst ts
  exact arrange_empty_mods_parenBalanced o singles a hs ha

end Solidity.Frontend.StatementGrammarH28
