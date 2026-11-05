import Solidity.Frontend.StatementGrammarH28.NoSemiPr

/-! Semicolon absence of immutable token combinators, with real literal fragment guards. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem semiFree_elem_atom (e : Elem) : SemiFree [.elem e] :=
  .token _ (by intro h; cases h)

theorem semiFree_elem (e : Elem) : SemiFree e.toks := by
  cases e <;> first
    | exact semiFree_elem_atom _
    | exact .append (semiFree_elem_atom _) (semiFree_kw _)

theorem semiFree_path (p : IdPath) : SemiFree p.toks := by
  have tail : ∀ ss : List String,
      SemiFree (ss.flatMap (fun s => [.punct .period, .ident s])) := by
    intro ss
    induction ss with
    | nil => exact .empty
    | cons s ss ih =>
      exact .append (.append
        (semiFree_punct .period (by intro h; cases h))
        (semiFree_id s)) ih
  exact .append (semiFree_id p.head) (tail p.tail)

theorem semiFree_visibility (v : Visibility) : SemiFree v.toks := by
  cases v <;> exact semiFree_kw _

theorem semiFree_mutability (v : Mutability) : SemiFree v.toks := by
  cases v <;> exact semiFree_kw _

theorem semiFree_dataLoc (v : DataLoc) : SemiFree v.toks := by
  cases v <;> exact semiFree_kw _

theorem litP_semiFree (l : Lit) : PrEnsures (litP l) SemiFree := by
  cases l with
  | str b => exact fragsP_semiFree _ _ (fun _ => .token _ (by intro h; cases h))
  | hexStr b => exact fragsP_semiFree _ _ (fun _ => .token _ (by intro h; cases h))
  | unicodeStr b => exact fragsP_semiFree _ _ (fun _ => .token _ (by intro h; cases h))
  | bool b => exact ensures_pure _ _ (.token _ (by intro h; cases h))
  | num n => exact ensures_pure _ _ (.token _ (by intro h; cases h))

theorem semiFree_prefix (op : PrefixOp) : SemiFree (op.punct) := by
  cases op <;> first
    | exact semiFree_kw _
    | exact semiFree_punct _ (by intro h; cases h)

theorem semiFree_suffix (op : SuffixOp) : SemiFree (pu op.punct) := by
  cases op <;> first
    | exact semiFree_kw _
    | exact semiFree_punct _ (by intro h; cases h)

theorem semiFree_mul (op : MulOp) : SemiFree (pu op.punct) := by
  cases op <;> first
    | exact semiFree_kw _
    | exact semiFree_punct _ (by intro h; cases h)

theorem semiFree_add (op : AddOp) : SemiFree (pu op.punct) := by
  cases op <;> first
    | exact semiFree_kw _
    | exact semiFree_punct _ (by intro h; cases h)

theorem semiFree_shift (op : ShiftOp) : SemiFree (pu op.punct) := by
  cases op <;> first
    | exact semiFree_kw _
    | exact semiFree_punct _ (by intro h; cases h)

theorem semiFree_order (op : OrderOp) : SemiFree (pu op.punct) := by
  cases op <;> first
    | exact semiFree_kw _
    | exact semiFree_punct _ (by intro h; cases h)

theorem semiFree_equality (op : EqOp) : SemiFree (pu op.punct) := by
  cases op <;> first
    | exact semiFree_kw _
    | exact semiFree_punct _ (by intro h; cases h)

theorem semiFree_assign (op : AssignOp) : SemiFree (pu op.punct) := by
  cases op <;> first
    | exact semiFree_kw _
    | exact semiFree_punct _ (by intro h; cases h)

theorem semiFree_single (slot : Slot) (ts : List Tok) (h : SemiFree ts) :
    ∀ pair ∈ single slot ts, SemiFree pair.2 := by
  unfold single
  split
  · intro pair hp; cases hp
  · intro pair hp
    have he : pair = (slot, ts) := List.mem_singleton.mp hp
    subst pair
    exact h

theorem arrange_empty_mods_semiFree (o : List Slot) :
    ∀ singles out, (∀ pair ∈ singles, SemiFree pair.2) →
      arrange o singles [] = some out → SemiFree out := by
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
        have tail : SemiFree rest := ih _ rest
          (fun p hp => hs p (List.mem_filter.mp hp).1) hr
        subst out
        exact .append (hs pair pairIn) tail

theorem attrsP_empty_mods_semiFree (singles : List (Slot × List Tok))
    (hs : ∀ pair ∈ singles, SemiFree pair.2) (o : List Slot) :
    PrEnsures (attrsP singles [] o) SemiFree := by
  intro L ts M he
  change (arrange o singles []).map (fun a => (a, L)) = some (ts, M) at he
  obtain ⟨a, ha, eq⟩ := Option.map_eq_some_iff.mp he
  have words : a = ts := congrArg Prod.fst eq
  subst ts
  exact arrange_empty_mods_semiFree o singles a hs ha

end Solidity.Frontend.StatementGrammarH28
