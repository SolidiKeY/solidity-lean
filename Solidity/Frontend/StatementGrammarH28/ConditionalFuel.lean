import Solidity.Frontend.StatementGrammarH28.ConditionalList

/-! Structural parser fuel for existing Boolean item-list syntax. All success
is derived from syntax witnesses and exact suffix frames, never assumed. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem boolean_statement_item_step {k : SCtx} {x : Syn (.stmt k)}
    {ts : List Tok} {d : Nat} (h : BooleanStatements x ts d) (n : Nat) (s : St)
    (frame : StatementFrame x s) :
    blockLeafStep (n + d + 7) k (locatedInput ts s) = .ok (some (.stmtItem x), s) := by
  have parse := boolean_statements_coverage h n s frame
  have lifted : ((stmt (n + d + 6) k (locatedInput ts s)).bind
      (fun p => .ok (Syn.stmtItem p.1, p.2))).bind
      (fun p => .ok (some p.1, p.2)) = .ok (some (.stmtItem x), s) := by
    rw [parse]
    rfl
  cases h with
  | loops hb => cases hb <;> simp only [blockLeafStep, item] <;> exact lifted
  | ifNone =>
    simp only [blockLeafStep, item]
    exact lifted
  | ifSome =>
    simp only [blockLeafStep, item]
    exact lifted
  | whileLoop =>
    simp only [blockLeafStep, item]
    exact lifted
  | forLoop =>
    simp only [blockLeafStep, item]
    exact lifted
  | doLoop =>
    simp only [blockLeafStep, item]
    exact lifted

inductive BooleanListBound : {k : SCtx} → Syn (.list (.item k)) → List (List Tok) → Nat → Prop where
  | nil {k : SCtx} : BooleanListBound (Syn.nil (c := .item k)) [] 0
  | cons {k : SCtx} {x : Syn (.stmt k)} {xs : Syn (.list (.item k))}
      {ts : List Tok} {parts : List (List Tok)} {d b : Nat} :
      BooleanStatements x ts d → BooleanListBound xs parts b →
      BooleanListBound (.cons (.stmtItem x) xs) (ts :: parts) (max (d + 7) b)

theorem boolean_list_bound_items {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} {b : Nat} (h : BooleanListBound xs parts b) :
    BooleanItemList xs parts := by
  induction h with
  | nil => exact .nil
  | cons hh ht ih => exact .cons hh ih

theorem boolean_item_list_has_bound {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} (h : BooleanItemList xs parts) :
    ∃ b, BooleanListBound xs parts b := by
  induction h with
  | nil => exact ⟨0, .nil⟩
  | @cons x xs ts parts d hh ht ih =>
    obtain ⟨b, hb⟩ := ih
    exact ⟨max (d + 7) b, .cons hh hb⟩

theorem boolean_item_list_count_le {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} (h : BooleanItemList xs parts) :
    itemCount xs ≤ parts.flatten.length := by
  induction h with
  | nil => exact Nat.le_refl 0
  | @cons x xs ts parts d hh ht ih =>
    have hn : ts.length ≠ 0 := by
      intro zero
      exact boolean_statement_tokens_nonempty hh (List.eq_nil_of_length_eq_zero zero)
    simp only [itemCount_cons, List.flatten_cons, List.length_append]
    omega

/-- Nesting fuel is a maximum over represented statements. The many-loop
counter is separately supplied from the intrinsic list length. -/
theorem boolean_list_items_at {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} {b : Nat} (h : BooleanListBound xs parts b)
    (fuel : Nat) (hf : b ≤ fuel) : ItemsAt xs parts.flatten fuel := by
  induction h generalizing fuel with
  | nil =>
    intro extra s
    simp only [itemCount_nil, itemsAsList_nil, List.flatten_nil]
    change manyAux _ (extra + 1) (endState s) = _
    exact many_aux_none (leaf_step_stop fuel k s)
  | @cons x xs ts parts d b hh ht ih =>
    intro extra s
    simp only [itemCount_cons, itemsAsList_cons, List.flatten_cons]
    change manyAux _ ((extra + itemCount xs + 1) + 1)
      (locatedInput (ts ++ parts.flatten) (endState s)) = _
    rw [locatedInput_append]
    have enough : d + 7 ≤ fuel := by omega
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' enough
    have eqfuel : fuel = n + d + 7 := by omega
    have frame : StatementFrame x (leafInput parts.flatten s) :=
      Or.inr (boolean_item_list_no_else (boolean_list_bound_items ht) (endState s)
        (by intro bad; cases bad))
    have head : blockLeafStep fuel k (locatedInput ts (leafInput parts.flatten s)) =
        .ok (some (.stmtItem x), leafInput parts.flatten s) := by
      rw [eqfuel]
      exact boolean_statement_item_step hh n (leafInput parts.flatten s) frame
    exact many_aux_cons head (ih fuel (by omega) extra s)

theorem boolean_list_block_coverage {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} {b : Nat} (h : BooleanListBound xs parts b) (n : Nat) (s : St) :
    block (n + b + 1) k (blockInput parts.flatten s) = .ok (.block xs, s) :=
  block_of_itemsAt xs parts.flatten (n + b)
    (boolean_item_list_count_le (boolean_list_bound_items h))
    (boolean_list_items_at h (n + b) (by omega)) s

theorem boolean_list_block_stmt_coverage {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} {b : Nat} (h : BooleanListBound xs parts b) (n : Nat) (s : St) :
    stmt (n + b + 2) k (blockInput parts.flatten s) = .ok (.blockStmt (.block xs), s) := by
  have hb := boolean_list_block_coverage h n s
  rw [blockInput_eq] at hb ⊢
  rw [stmt_block_prefix, hb]
  rfl

theorem boolean_list_unchecked_coverage {l : Bool} {xs : Syn (.list (.item ⟨l, true⟩))}
    {parts : List (List Tok)} {b : Nat} (h : BooleanListBound xs parts b) (n : Nat) (s : St) :
    item (n + b + 2) ⟨l, false⟩ (uncheckedInput parts.flatten s) =
      .ok (.uncheckedItem (.block xs), s) := by
  rw [uncheckedInput_eq, item_unchecked_prefix, boolean_list_block_coverage h]
  rfl

/-- Every existing unbounded list witness constructs a sufficient fuel bound;
no successful parse, external fuel oracle or expression uniqueness is assumed. -/
theorem boolean_item_list_block_complete {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} (h : BooleanItemList xs parts) :
    ∃ b, ∀ n s, block (n + b + 1) k (blockInput parts.flatten s) = .ok (.block xs, s) := by
  obtain ⟨b, hb⟩ := boolean_item_list_has_bound h
  exact ⟨b, boolean_list_block_coverage hb⟩

#print axioms boolean_list_bound_items
#print axioms boolean_item_list_has_bound
#print axioms boolean_item_list_count_le
#print axioms boolean_list_items_at
#print axioms boolean_list_block_coverage
#print axioms boolean_list_block_stmt_coverage
#print axioms boolean_list_unchecked_coverage
#print axioms boolean_item_list_block_complete
#print axioms boolean_statement_item_step
end Solidity.Frontend.StatementGrammarH28
