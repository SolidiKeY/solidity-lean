import Solidity.Frontend.StatementGrammarH28.BalancePr

/-! H31 local proofs about immutable literal/type/attribute token combinators.
Token payloads are atoms; no expression uniqueness is asserted. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem balanced_elem_atom (e : Elem) : BraceBalanced [.elem e] :=
  .token _ (by intro h; cases h) (by intro h; cases h)

theorem balanced_elem (e : Elem) : BraceBalanced e.toks := by
  cases e <;> first
    | exact balanced_elem_atom _
    | exact .append (balanced_elem_atom _) (balanced_kw _)

theorem balanced_path (p : IdPath) : BraceBalanced p.toks := by
  have tail : ∀ ss : List String,
      BraceBalanced (ss.flatMap (fun s => [.punct .period, .ident s])) := by
    intro ss
    induction ss with
    | nil => exact .empty
    | cons s ss ih =>
      exact .append (.append
        (balanced_punct .period (by intro h; cases h) (by intro h; cases h))
        (balanced_id s)) ih
  exact .append (balanced_id p.head) (tail p.tail)

theorem balanced_visibility (v : Visibility) : BraceBalanced v.toks := by
  cases v <;> exact balanced_kw _

theorem balanced_mutability (v : Mutability) : BraceBalanced v.toks := by
  cases v <;> exact balanced_kw _

theorem balanced_dataLoc (v : DataLoc) : BraceBalanced v.toks := by
  cases v <;> exact balanced_kw _

theorem balanced_yulLit (l : YulLit) : BraceBalanced l.toks := by
  cases l <;> exact .token _ (by intro h; cases h) (by intro h; cases h)

theorem litP_balanced (l : Lit) : PrEnsures (litP l) BraceBalanced := by
  cases l with
  | str b => exact fragsP_balanced _ _ (fun _ => .token _ (by intro h; cases h) (by intro h; cases h))
  | hexStr b => exact fragsP_balanced _ _ (fun _ => .token _ (by intro h; cases h) (by intro h; cases h))
  | unicodeStr b => exact fragsP_balanced _ _ (fun _ => .token _ (by intro h; cases h) (by intro h; cases h))
  | bool b => exact ensures_pure _ _ (.token _ (by intro h; cases h) (by intro h; cases h))
  | num n => exact ensures_pure _ _ (.token _ (by intro h; cases h) (by intro h; cases h))

theorem balanced_prefix (op : PrefixOp) : BraceBalanced (op.punct) := by
  cases op <;> first
    | exact balanced_kw _
    | exact balanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem balanced_suffix (op : SuffixOp) : BraceBalanced (pu op.punct) := by
  cases op <;> first
    | exact balanced_kw _
    | exact balanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem balanced_mul (op : MulOp) : BraceBalanced (pu op.punct) := by
  cases op <;> first
    | exact balanced_kw _
    | exact balanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem balanced_add (op : AddOp) : BraceBalanced (pu op.punct) := by
  cases op <;> first
    | exact balanced_kw _
    | exact balanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem balanced_shift (op : ShiftOp) : BraceBalanced (pu op.punct) := by
  cases op <;> first
    | exact balanced_kw _
    | exact balanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem balanced_order (op : OrderOp) : BraceBalanced (pu op.punct) := by
  cases op <;> first
    | exact balanced_kw _
    | exact balanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem balanced_equality (op : EqOp) : BraceBalanced (pu op.punct) := by
  cases op <;> first
    | exact balanced_kw _
    | exact balanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem balanced_assign (op : AssignOp) : BraceBalanced (pu op.punct) := by
  cases op <;> first
    | exact balanced_kw _
    | exact balanced_punct _ (by intro h; cases h) (by intro h; cases h)

theorem balanced_single (slot : Slot) (ts : List Tok) (h : BraceBalanced ts) :
    ∀ pair ∈ single slot ts, BraceBalanced pair.2 := by
  unfold single
  split
  · intro pair hp; cases hp
  · intro pair hp
    have he : pair = (slot, ts) := List.mem_singleton.mp hp
    subst pair
    exact h

theorem arrange_empty_mods_balanced (o : List Slot) :
    ∀ singles out, (∀ pair ∈ singles, BraceBalanced pair.2) →
      arrange o singles [] = some out → BraceBalanced out := by
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
        have tail : BraceBalanced rest := ih _ rest
          (fun p hp => hs p (List.mem_filter.mp hp).1) hr
        subst out
        exact .append (hs pair pairIn) tail

theorem attrsP_empty_mods_balanced (singles : List (Slot × List Tok))
    (hs : ∀ pair ∈ singles, BraceBalanced pair.2) (o : List Slot) :
    PrEnsures (attrsP singles [] o) BraceBalanced := by
  intro L ts M he
  change (arrange o singles []).map (fun a => (a, L)) = some (ts, M) at he
  obtain ⟨a, ha, eq⟩ := Option.map_eq_some_iff.mp he
  have words : a = ts := congrArg Prod.fst eq
  subst ts
  exact arrange_empty_mods_balanced o singles a hs ha

#print axioms balanced_elem_atom
#print axioms balanced_elem
#print axioms balanced_path
#print axioms balanced_visibility
#print axioms balanced_mutability
#print axioms balanced_dataLoc
#print axioms balanced_yulLit
#print axioms litP_balanced
#print axioms balanced_prefix
#print axioms balanced_suffix
#print axioms balanced_mul
#print axioms balanced_add
#print axioms balanced_shift
#print axioms balanced_order
#print axioms balanced_equality
#print axioms balanced_assign
#print axioms balanced_single
#print axioms arrange_empty_mods_balanced
#print axioms attrsP_empty_mods_balanced
end Solidity.Frontend.StatementGrammarH28
