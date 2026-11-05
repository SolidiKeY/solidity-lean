import Solidity.Frontend.StatementGrammarH28.BlockLeafCoverage

/-! Syntax-derived nesting fuel for recursive control/block item lists.
No expressions or producer interfaces are changed. Zero internal locations,
arbitrary suffix/layout/EOF, as in the existing control-leaf coverage. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

inductive NestedItems : {k : SCtx} → Syn (.list (.item k)) → List Tok → Nat → Prop where
  | nil {k : SCtx} : NestedItems (Syn.nil (c := .item k)) [] 0
  | returnCons {k : SCtx} {xs : Syn (.list (.item k))} {ts : List Tok} {d : Nat} :
      NestedItems xs ts d → NestedItems (.cons (.stmtItem (.returnStmt .none)) xs)
        (.kw .return_ :: .punct .semi :: ts) d
  | breakCons {u : Bool} {xs : Syn (.list (.item ⟨true, u⟩))} {ts : List Tok} {d : Nat} :
      NestedItems xs ts d → NestedItems (.cons (.stmtItem .breakStmt) xs)
        (.kw .break_ :: .punct .semi :: ts) d
  | continueCons {u : Bool} {xs : Syn (.list (.item ⟨true, u⟩))} {ts : List Tok} {d : Nat} :
      NestedItems xs ts d → NestedItems (.cons (.stmtItem .continueStmt) xs)
        (.kw .continue_ :: .punct .semi :: ts) d
  | blockCons {k : SCtx} {ys xs : Syn (.list (.item k))} {bs ts : List Tok} {b d : Nat} :
      NestedItems ys bs b → NestedItems xs ts d →
      NestedItems (.cons (.stmtItem (.blockStmt (.block ys))) xs)
        (braces bs ++ ts) (max (b + 3) d)
  | uncheckedCons {l : Bool} {ys : Syn (.list (.item ⟨l, true⟩))}
      {xs : Syn (.list (.item ⟨l, false⟩))} {bs ts : List Tok} {b d : Nat} :
      NestedItems ys bs b → NestedItems xs ts d →
      NestedItems (.cons (.uncheckedItem (.block ys)) xs)
        ((.kw .unchecked :: braces bs) ++ ts) (max (b + 2) d)

theorem nested_items_count_le {k : SCtx} {xs : Syn (.list (.item k))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) : itemCount xs ≤ ts.length := by
  induction h with
  | nil => simp only [itemCount_nil, itemCount_cons, List.length_nil, Nat.le_refl]
  | returnCons h ih => simp only [itemCount_nil, itemCount_cons, List.length_cons]; omega
  | breakCons h ih => simp only [itemCount_nil, itemCount_cons, List.length_cons]; omega
  | continueCons h ih => simp only [itemCount_nil, itemCount_cons, List.length_cons]; omega
  | blockCons hb ht ihb iht =>
    simp only [itemCount_nil, itemCount_cons, braces, pu, List.length_append, List.length_cons, List.length_nil]
    omega
  | uncheckedCons hb ht ihb iht =>
    simp only [itemCount_nil, itemCount_cons, braces, pu, List.length_append, List.length_cons, List.length_nil]
    omega

def ItemsAt {k : SCtx} (xs : Syn (.list (.item k))) (ts : List Tok) (fuel : Nat) : Prop :=
  ∀ extra s, manyAux (blockLeafStep fuel k) (extra + itemCount xs + 1) (leafInput ts s) =
    .ok (itemsAsList xs, endState s)

theorem locatedInput_append (head tail : List Tok) (s : St) :
    locatedInput (head ++ tail) s = locatedInput head (locatedInput tail s) := by
  simp only [locatedInput, List.map_append, List.append_assoc]

theorem itemsAt_cons {k : SCtx} (x : Syn (.item k)) (xs : Syn (.list (.item k)))
    (head tail : List Tok) (fuel : Nat)
    (hh : ∀ s, blockLeafStep fuel k (locatedInput head s) = .ok (some x, s))
    (ht : ItemsAt xs tail fuel) : ItemsAt (.cons x xs) (head ++ tail) fuel := by
  intro extra s
  simp only [itemCount_nil, itemCount_cons, itemsAsList_nil, itemsAsList_cons]
  change manyAux _ ((extra + itemCount xs + 1) + 1)
    (locatedInput (head ++ tail) (endState s)) = _
  rw [locatedInput_append]
  exact many_aux_cons (hh (leafInput tail s)) (ht extra s)

theorem block_of_itemsAt {k : SCtx} (xs : Syn (.list (.item k))) (ts : List Tok)
    (fuel : Nat) (hc : itemCount xs ≤ ts.length) (h : ItemsAt xs ts fuel) (s : St) :
    block (fuel + 1) k (blockInput ts s) = .ok (Syn.block xs, s) := by
  have hf : itemCount xs + 1 ≤ (leafInput ts s).ts.length + 1 := by
    simp only [leafInput, locatedInput, endState, List.length_append, List.length_map,
      List.length_cons]
    omega
  obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le' hf
  have he' : (leafInput ts s).ts.length + 1 = extra + itemCount xs + 1 := by omega
  rw [blockInput_eq]
  simp only [block]
  change (manyAux (blockLeafStep fuel k) ((leafInput ts s).ts.length + 1)
    (leafInput ts s)).bind (fun p =>
      ((do expectP .rbrace; pure (Syn.block (toSynList p.1))) : P (Syn (.block k))) p.2) = _
  rw [he', h extra s]
  change (Except.ok (Syn.block (toSynList (itemsAsList xs)), s) :
    Except Error (Syn (.block k) × St)) = _
  rw [itemsAsList_inverse]

theorem step_block_of_coverage (n : Nat) (k : SCtx) (b : Syn (.block k))
    (ts : List Tok) (s : St) (hb : block n k (blockInput ts s) = .ok (b, s)) :
    blockLeafStep (n + 2) k (blockInput ts s) =
      .ok (some (.stmtItem (.blockStmt b)), s) := by
  rw [blockInput_eq] at hb ⊢
  have hs : stmt (n + 1) k { (leafInput ts s) with
      ts := atToken (.punct .lbrace) 0 0 :: (leafInput ts s).ts } =
      .ok (.blockStmt b, s) := by
    rw [stmt_block_prefix, hb]
    rfl
  have hi : item (n + 2) k { (leafInput ts s) with
      ts := atToken (.punct .lbrace) 0 0 :: (leafInput ts s).ts } =
      .ok (.stmtItem (.blockStmt b), s) := by
    simp only [item]
    change (stmt (n + 1) k _).bind (fun p => .ok (Syn.stmtItem p.1, p.2)) = _
    rw [hs]
    rfl
  simp only [blockLeafStep]
  change (item (n + 2) k _).bind (fun p => .ok (some p.1, p.2)) = _
  rw [hi]
  rfl

theorem step_unchecked_of_coverage (n : Nat) (l : Bool)
    (b : Syn (.block ⟨l, true⟩)) (ts : List Tok) (s : St)
    (hb : block n ⟨l, true⟩ (blockInput ts s) = .ok (b, s)) :
    blockLeafStep (n + 1) ⟨l, false⟩ (uncheckedInput ts s) =
      .ok (some (.uncheckedItem b), s) := by
  rw [uncheckedInput_eq]
  simp only [blockLeafStep]
  change (item (n + 1) ⟨l, false⟩ _).bind (fun p => .ok (some p.1, p.2)) = _
  rw [item_unchecked_prefix, hb]
  rfl

/-- Every parsing success used by composition is derived recursively from
NestedItems; the final theorem has no assumed successful parse premise. -/
theorem nested_items_at {k : SCtx} {xs : Syn (.list (.item k))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) :
    ∀ fuel, d + 3 ≤ fuel → ItemsAt xs ts fuel := by
  induction h with
  | nil =>
    intro fuel hf extra s
    simp only [itemsAsList_nil, itemsAsList_cons, itemCount_nil, itemCount_cons]
    change manyAux (blockLeafStep fuel _) (extra + 1) (endState s) = _
    exact many_aux_none (leaf_step_stop _ _ _)
  | @returnCons k xs ts d ht ih =>
    intro fuel hf
    obtain ⟨n, he⟩ := Nat.exists_eq_add_of_le' (show 3 ≤ fuel by omega)
    subst fuel
    apply itemsAt_cons (Syn.stmtItem (.returnStmt .none)) xs
      [.kw .return_, .punct .semi] ts (n + 3)
    · intro s
      exact leaf_step_return n k s
    · exact ih (n + 3) hf
  | @breakCons u xs ts d ht ih =>
    intro fuel hf
    obtain ⟨n, he⟩ := Nat.exists_eq_add_of_le' (show 3 ≤ fuel by omega)
    subst fuel
    apply itemsAt_cons (Syn.stmtItem .breakStmt) xs
      [.kw .break_, .punct .semi] ts (n + 3)
    · intro s
      exact leaf_step_break n u s
    · exact ih (n + 3) hf
  | @continueCons u xs ts d ht ih =>
    intro fuel hf
    obtain ⟨n, he⟩ := Nat.exists_eq_add_of_le' (show 3 ≤ fuel by omega)
    subst fuel
    apply itemsAt_cons (Syn.stmtItem .continueStmt) xs
      [.kw .continue_, .punct .semi] ts (n + 3)
    · intro s
      exact leaf_step_continue n u s
    · exact ih (n + 3) hf
  | @blockCons k ys xs bs ts b d hb ht ihb iht =>
    intro fuel hf
    apply itemsAt_cons (Syn.stmtItem (.blockStmt (.block ys))) xs (braces bs) ts fuel
    · intro s
      have enough : b + 6 ≤ fuel := by omega
      obtain ⟨n, he⟩ := Nat.exists_eq_add_of_le' enough
      have he' : fuel = (n + b + 3 + 1) + 2 := by omega
      rw [he']
      exact step_block_of_coverage (n + b + 3 + 1) k (.block ys) bs s
        (block_of_itemsAt ys bs (n + b + 3) (nested_items_count_le hb)
          (ihb (n + b + 3) (by omega)) s)
    · exact iht fuel (by omega)
  | @uncheckedCons l ys xs bs ts b d hb ht ihb iht =>
    intro fuel hf
    apply itemsAt_cons (Syn.uncheckedItem (.block ys)) xs
      (.kw .unchecked :: braces bs) ts fuel
    · intro s
      have enough : b + 5 ≤ fuel := by omega
      obtain ⟨n, he⟩ := Nat.exists_eq_add_of_le' enough
      have he' : fuel = (n + b + 3 + 1) + 1 := by omega
      rw [he']
      exact step_unchecked_of_coverage (n + b + 3 + 1) l (.block ys) bs s
        (block_of_itemsAt ys bs (n + b + 3) (nested_items_count_le hb)
          (ihb (n + b + 3) (by omega)) s)
    · exact iht fuel (by omega)

/-- Sufficient nesting fuel is derived from the indexed syntax relation:
three units per ordinary nested block, two per unchecked wrapper. List-loop
fuel is independently derived from the actual token length. -/
theorem nested_block_coverage {k : SCtx} {xs : Syn (.list (.item k))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (n : Nat) (s : St) :
    block (n + d + 4) k (blockInput ts s) = .ok (Syn.block xs, s) :=
  block_of_itemsAt xs ts (n + d + 3) (nested_items_count_le h)
    (nested_items_at h (n + d + 3) (by omega)) s

theorem nested_block_stmt_coverage {k : SCtx} {xs : Syn (.list (.item k))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (n : Nat) (s : St) :
    stmt (n + d + 5) k (blockInput ts s) = .ok (.blockStmt (.block xs), s) := by
  have hb := nested_block_coverage h n s
  rw [blockInput_eq] at hb ⊢
  rw [stmt_block_prefix, hb]
  rfl

theorem nested_unchecked_coverage {l : Bool} {xs : Syn (.list (.item ⟨l, true⟩))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (n : Nat) (s : St) :
    item (n + d + 5) ⟨l, false⟩ (uncheckedInput ts s) =
      .ok (.uncheckedItem (.block xs), s) := by
  rw [uncheckedInput_eq, item_unchecked_prefix, nested_block_coverage h]
  rfl

theorem keyword_semi_balanced (kw : Kw) : BraceBalanced [.kw kw, .punct .semi] :=
  .append (.token _ (by intro h; cases h) (by intro h; cases h))
    (.token _ (by intro h; cases h) (by intro h; cases h))

theorem nested_tokens_balanced {k : SCtx} {xs : Syn (.list (.item k))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) : BraceBalanced ts := by
  induction h with
  | nil => exact .empty
  | returnCons ht ih => exact .append (keyword_semi_balanced .return_) ih
  | breakCons ht ih => exact .append (keyword_semi_balanced .break_) ih
  | continueCons ht ih => exact .append (keyword_semi_balanced .continue_) ih
  | blockCons hb ht ihb iht => exact .append (.wrap ihb) iht
  | uncheckedCons hb ht ihb iht =>
    exact .append (.append (.token _ (by intro h; cases h) (by intro h; cases h))
      (.wrap ihb)) iht

theorem block_yield_of_flat {k : SCtx} (xs : Syn (.list (.item k)))
    (ts : List Tok) (L : List Choice)
    (h : (xs.yield L).map (fun p => (p.1.flatten, p.2)) = some (ts, L)) :
    (Syn.block xs).yield L = some ([braces ts], L) := by
  obtain ⟨⟨parts, M⟩, hy, he⟩ := Option.map_eq_some_iff.mp h
  have layouts : M = L := congrArg Prod.snd he
  subst M
  have hb := block_yield_of_items xs L L parts hy
  have words : parts.flatten = ts := congrArg Prod.fst he
  rw [words] at hb
  exact hb

theorem nested_items_yield {k : SCtx} {xs : Syn (.list (.item k))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (L : List Choice) :
    (xs.yield L).map (fun p => (p.1.flatten, p.2)) = some (ts, L) := by
  induction h with
  | nil => rfl
  | @returnCons k xs ts d ht ih =>
    exact flat_list_yield_cons (Syn.stmtItem (k := k) (.returnStmt .none)) xs L
      [.kw .return_, .punct .semi] ts rfl ih
  | @breakCons u xs ts d ht ih =>
    exact flat_list_yield_cons (Syn.stmtItem (k := ⟨true, u⟩) .breakStmt) xs L
      [.kw .break_, .punct .semi] ts rfl ih
  | @continueCons u xs ts d ht ih =>
    exact flat_list_yield_cons (Syn.stmtItem (k := ⟨true, u⟩) .continueStmt) xs L
      [.kw .continue_, .punct .semi] ts rfl ih
  | @blockCons k ys xs bs ts b d hb ht ihb iht =>
    exact flat_list_yield_cons (Syn.stmtItem (.blockStmt (.block ys))) xs L
      (braces bs) ts (block_yield_of_flat ys bs L ihb) iht
  | @uncheckedCons l ys xs bs ts b d hb ht ihb iht =>
    apply flat_list_yield_cons (Syn.uncheckedItem (.block ys)) xs L
      (.kw .unchecked :: braces bs) ts ?_ iht
    have hbody := block_yield_of_flat ys bs L ihb
    simp only [Syn.yield]
    change ((Syn.block ys).yield L).bind (fun p =>
      some ([[Tok.kw .unchecked] ++ p.1.flatten], p.2)) = _
    rw [hbody]
    simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.cons_append, List.nil_append]

theorem nested_block_yield {k : SCtx} {xs : Syn (.list (.item k))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (L : List Choice) :
    (Syn.block xs).yield L = some ([braces ts], L) :=
  block_yield_of_flat xs ts L (nested_items_yield h L)

theorem nested_block_boundary {k : SCtx} {xs : Syn (.list (.item k))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (L : List Choice) :
    BlockBoundary (Syn.block xs) L L ts :=
  ⟨nested_block_yield h L, nested_tokens_balanced h⟩

theorem leaf_to_nested {k : SCtx} {xs : Syn (.list (.item k))} {ts : List Tok}
    (h : LeafItems xs ts) : NestedItems xs ts 0 := by
  induction h with
  | nil => exact .nil
  | returnCons ht ih => exact .returnCons ih
  | breakCons ht ih => exact .breakCons ih
  | continueCons ht ih => exact .continueCons ih

#print axioms leaf_to_nested
#print axioms keyword_semi_balanced
#print axioms nested_tokens_balanced
#print axioms block_yield_of_flat
#print axioms nested_items_yield
#print axioms nested_block_yield
#print axioms nested_block_boundary
#print axioms nested_items_at
#print axioms nested_block_coverage
#print axioms nested_block_stmt_coverage
#print axioms nested_unchecked_coverage
#print axioms nested_items_count_le
#print axioms locatedInput_append
#print axioms itemsAt_cons
#print axioms block_of_itemsAt
#print axioms step_block_of_coverage
#print axioms step_unchecked_of_coverage
end Solidity.Frontend.StatementGrammarH28
