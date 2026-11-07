import Solidity.Frontend.StatementGrammarH28.LeafCoverage
import Solidity.Frontend.StatementGrammarH28.YieldSplit
import Solidity.Frontend.StatementGrammarH28.G0List

/-!
# Structural list fuel for blocks of control leaves

The relation below is indexed by existing Syn item lists. It covers arbitrary
list lengths of empty return, break and continue in their intrinsic contexts;
it is not a replacement AST or a claim about all compound statements.
-/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def locatedInput (ts : List Tok) (s : St) : St :=
  { s with ts := ts.map (fun t => atToken t 0 0) ++ s.ts }

def itemCount {c : Cat} (xs : Syn (.list c)) : Nat := g0ListLength xs

def itemsAsList {c : Cat} (xs : Syn (.list c)) : List (Syn c) := g0ListValues xs

theorem itemCount_nil {c : Cat} : itemCount (Syn.nil (c := c)) = 0 := rfl

theorem itemCount_cons {c : Cat} (x : Syn c) (xs : Syn (.list c)) :
    itemCount (.cons x xs) = itemCount xs + 1 := rfl

theorem itemsAsList_nil {c : Cat} : itemsAsList (Syn.nil (c := c)) = [] := rfl

theorem itemsAsList_cons {c : Cat} (x : Syn c) (xs : Syn (.list c)) :
    itemsAsList (.cons x xs) = x :: itemsAsList xs := rfl

theorem itemsAsList_inverse : {c : Cat} → (xs : Syn (.list c)) →
    toSynList (itemsAsList xs) = xs
  | _, .nil => by simp only [itemsAsList_nil, itemsAsList_cons, toSynList]
  | _, .cons x xs => by
    simp only [itemsAsList_nil, itemsAsList_cons, toSynList]
    exact congrArg (Syn.cons x) (itemsAsList_inverse xs)

inductive LeafItems : {k : SCtx} → Syn (.list (.item k)) → List Tok → Prop where
  | nil {k : SCtx} : LeafItems (Syn.nil (c := .item k)) []
  | returnCons {k : SCtx} {xs : Syn (.list (.item k))} {ts : List Tok} :
      LeafItems xs ts → LeafItems (.cons (.stmtItem (.returnStmt .none)) xs)
        (.kw .return_ :: .punct .semi :: ts)
  | breakCons {u : Bool} {xs : Syn (.list (.item ⟨true, u⟩))} {ts : List Tok} :
      LeafItems xs ts → LeafItems (.cons (.stmtItem .breakStmt) xs)
        (.kw .break_ :: .punct .semi :: ts)
  | continueCons {u : Bool} {xs : Syn (.list (.item ⟨true, u⟩))} {ts : List Tok} :
      LeafItems xs ts → LeafItems (.cons (.stmtItem .continueStmt) xs)
        (.kw .continue_ :: .punct .semi :: ts)

/-- This is exactly the step used by the existing block parser's many loop. -/
def blockLeafStep (n : Nat) (k : SCtx) : P (Option (Syn (.item k))) := do
  if ← isP .rbrace then return none
  match ← peek with
  | none => return none
  | _ => return some (← item n k)

theorem leaf_step_return (n : Nat) (k : SCtx) (s : St) :
    blockLeafStep (n + 3) k (controlInput (.kw .return_) 0 0 0 0 s) =
      .ok (some (.stmtItem (.returnStmt .none)), s) := by
  simp only [blockLeafStep, item]
  change (stmt (n + 2) k (controlInput (.kw .return_) 0 0 0 0 s)).bind
    (fun p => .ok (some (Syn.stmtItem p.1), p.2)) = _
  rw [empty_return_coverage]
  rfl

theorem leaf_step_break (n : Nat) (u : Bool) (s : St) :
    blockLeafStep (n + 3) ⟨true, u⟩ (controlInput (.kw .break_) 0 0 0 0 s) =
      .ok (some (.stmtItem .breakStmt), s) := by
  simp only [blockLeafStep, item]
  change (stmt ((n + 1) + 1) ⟨true, u⟩ (controlInput (.kw .break_) 0 0 0 0 s)).bind
    (fun p => .ok (some (Syn.stmtItem p.1), p.2)) = _
  rw [break_coverage]
  rfl

theorem leaf_step_continue (n : Nat) (u : Bool) (s : St) :
    blockLeafStep (n + 3) ⟨true, u⟩ (controlInput (.kw .continue_) 0 0 0 0 s) =
      .ok (some (.stmtItem .continueStmt), s) := by
  simp only [blockLeafStep, item]
  change (stmt ((n + 1) + 1) ⟨true, u⟩ (controlInput (.kw .continue_) 0 0 0 0 s)).bind
    (fun p => .ok (some (Syn.stmtItem p.1), p.2)) = _
  rw [continue_coverage]
  rfl

theorem leaf_step_stop (n : Nat) (k : SCtx) (s : St) :
    blockLeafStep n k { s with ts := atToken (.punct .rbrace) 0 0 :: s.ts } =
      .ok (none, { s with ts := atToken (.punct .rbrace) 0 0 :: s.ts }) := by rfl

def endState (s : St) : St :=
  { s with ts := atToken (.punct .rbrace) 0 0 :: s.ts }

def leafInput (ts : List Tok) (s : St) : St := locatedInput ts (endState s)

theorem leaf_items_token_length {k : SCtx} {xs : Syn (.list (.item k))} {ts : List Tok}
    (h : LeafItems xs ts) : ts.length = itemCount xs + itemCount xs := by
  induction h with
  | nil => simp only [List.length_nil, itemCount_nil, itemCount_cons, Nat.add_zero]
  | returnCons h ih =>
    simp only [List.length_cons, itemCount_nil, itemCount_cons, ih, Nat.add_succ, Nat.succ_add]
  | breakCons h ih =>
    simp only [List.length_cons, itemCount_nil, itemCount_cons, ih, Nat.add_succ, Nat.succ_add]
  | continueCons h ih =>
    simp only [List.length_cons, itemCount_nil, itemCount_cons, ih, Nat.add_succ, Nat.succ_add]

/-- Operational composition lemma; its premises are discharged by the
concrete step equations in the constructor-completeness proof below. -/
theorem many_aux_none {α : Type} {p : P (Option α)} {n : Nat} {s out : St}
    (hp : p s = .ok (none, out)) : manyAux p (n + 1) s = .ok ([], out) := by
  simp only [manyAux]
  change (p s).bind (fun z =>
    ((match z.1 with
      | some a => do
        let r ← manyAux p n
        pure (a :: r)
      | none => pure []) : P (List α)) z.2) = _
  rw [hp]
  rfl

theorem many_aux_cons {α : Type} {p : P (Option α)} {n : Nat} {s mid out : St}
    {a : α} {rest : List α} (hp : p s = .ok (some a, mid))
    (hr : manyAux p n mid = .ok (rest, out)) :
    manyAux p (n + 1) s = .ok (a :: rest, out) := by
  simp only [manyAux]
  change (p s).bind (fun z =>
    ((match z.1 with
      | some a => do
        let r ← manyAux p n
        pure (a :: r)
      | none => pure []) : P (List α)) z.2) = _
  rw [hp]
  change (manyAux p n mid).bind (fun q => .ok (a :: q.1, q.2)) = _
  rw [hr]
  rfl

/-- Arbitrarily long intrinsic control-leaf lists need one loop step per
item plus the stopping step. There is no assumed successful parse premise. -/
theorem leaf_items_many_aux {k : SCtx} {xs : Syn (.list (.item k))} {ts : List Tok}
    (h : LeafItems xs ts) (n extra : Nat) (s : St) :
    manyAux (blockLeafStep (n + 3) k) (extra + itemCount xs + 1) (leafInput ts s) =
      .ok (itemsAsList xs, endState s) := by
  induction h generalizing n extra s with
  | nil =>
    simp only [itemCount_nil, itemCount_cons, itemsAsList_nil, itemsAsList_cons]
    change manyAux (blockLeafStep (n + 3) _) (extra + 1) (endState s) = _
    exact many_aux_none (leaf_step_stop _ _ _)
  | @returnCons k xs ts hx ih =>
    simp only [itemCount_nil, itemCount_cons, itemsAsList_nil, itemsAsList_cons]
    change manyAux (blockLeafStep (n + 3) k) ((extra + itemCount xs + 1) + 1)
      (controlInput (.kw .return_) 0 0 0 0 (leafInput ts s)) = _
    exact many_aux_cons (leaf_step_return n k (leafInput ts s)) (ih n extra s)
  | @breakCons u xs ts hx ih =>
    simp only [itemCount_nil, itemCount_cons, itemsAsList_nil, itemsAsList_cons]
    change manyAux (blockLeafStep (n + 3) ⟨true, u⟩) ((extra + itemCount xs + 1) + 1)
      (controlInput (.kw .break_) 0 0 0 0 (leafInput ts s)) = _
    exact many_aux_cons (leaf_step_break n u (leafInput ts s)) (ih n extra s)
  | @continueCons u xs ts hx ih =>
    simp only [itemCount_nil, itemCount_cons, itemsAsList_nil, itemsAsList_cons]
    change manyAux (blockLeafStep (n + 3) ⟨true, u⟩) ((extra + itemCount xs + 1) + 1)
      (controlInput (.kw .continue_) 0 0 0 0 (leafInput ts s)) = _
    exact many_aux_cons (leaf_step_continue n u (leafInput ts s)) (ih n extra s)

/-- The parser's actual token-derived many fuel is sufficient for every
list admitted by LeafItems. The bound is proved from syntax/token length. -/
theorem leaf_items_many {k : SCtx} {xs : Syn (.list (.item k))} {ts : List Tok}
    (h : LeafItems xs ts) (n : Nat) (s : St) :
    many (blockLeafStep (n + 3) k) (leafInput ts s) =
      .ok (itemsAsList xs, endState s) := by
  have fuel : (leafInput ts s).ts.length + 1 =
      (itemCount xs + s.ts.length + 1) + itemCount xs + 1 := by
    simp only [leafInput, locatedInput, endState, List.length_append, List.length_map,
      List.length_cons, leaf_items_token_length h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  change manyAux _ ((leafInput ts s).ts.length + 1) _ = _
  rw [fuel]
  exact leaf_items_many_aux h n (itemCount xs + s.ts.length + 1) s

def blockInput (ts : List Tok) (s : St) : St := locatedInput (braces ts) s

theorem blockInput_eq (ts : List Tok) (s : St) :
    blockInput ts s = { (leafInput ts s) with
      ts := atToken (.punct .lbrace) 0 0 :: (leafInput ts s).ts } := by
  simp only [blockInput, leafInput, locatedInput, endState, braces, pu,
    List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]

/-- The constant structural bound is four for this nonrecursive leaf grammar;
list length is handled by the proved token-derived many bound, not assumed success. -/
theorem leaf_block_coverage {k : SCtx} {xs : Syn (.list (.item k))} {ts : List Tok}
    (h : LeafItems xs ts) (n : Nat) (s : St) :
    block (n + 4) k (blockInput ts s) = .ok (Syn.block xs, s) := by
  rw [blockInput_eq]
  simp only [block]
  change (many (blockLeafStep (n + 3) k) (leafInput ts s)).bind (fun p =>
    ((do
      expectP .rbrace
      pure (Syn.block (toSynList p.1))) : P (Syn (.block k))) p.2) = _
  rw [leaf_items_many h]
  change (Except.ok (Syn.block (toSynList (itemsAsList xs)), s) :
    Except Error (Syn (.block k) × St)) = .ok (Syn.block xs, s)
  rw [itemsAsList_inverse]

theorem stmt_block_prefix (n : Nat) (k : SCtx) (s : St) :
    stmt (n + 1) k { s with ts := atToken (.punct .lbrace) 0 0 :: s.ts } =
      (block n k { s with ts := atToken (.punct .lbrace) 0 0 :: s.ts }).bind
        (fun p => .ok (Syn.blockStmt p.1, p.2)) := by
  simp only [stmt]
  rfl

theorem leaf_block_stmt_coverage {k : SCtx} {xs : Syn (.list (.item k))} {ts : List Tok}
    (h : LeafItems xs ts) (n : Nat) (s : St) :
    stmt (n + 5) k (blockInput ts s) = .ok (Syn.blockStmt (Syn.block xs), s) := by
  have hb := leaf_block_coverage h n s
  rw [blockInput_eq] at hb
  rw [blockInput_eq, stmt_block_prefix, hb]
  rfl

def uncheckedInput (ts : List Tok) (s : St) : St :=
  locatedInput (.kw .unchecked :: braces ts) s

theorem uncheckedInput_eq (ts : List Tok) (s : St) :
    uncheckedInput ts s = { (blockInput ts s) with
      ts := atToken (.kw .unchecked) 0 0 :: (blockInput ts s).ts } := by rfl

theorem item_unchecked_prefix (n : Nat) (l : Bool) (s : St) :
    item (n + 1) ⟨l, false⟩ { s with ts := atToken (.kw .unchecked) 0 0 :: s.ts } =
      (block n ⟨l, true⟩ s).bind (fun p => .ok (Syn.uncheckedItem p.1, p.2)) := by
  simp only [item]
  rfl

theorem leaf_unchecked_coverage {l : Bool} {xs : Syn (.list (.item ⟨l, true⟩))} {ts : List Tok}
    (h : LeafItems xs ts) (n : Nat) (s : St) :
    item (n + 5) ⟨l, false⟩ (uncheckedInput ts s) =
      .ok (Syn.uncheckedItem (Syn.block xs), s) := by
  rw [uncheckedInput_eq, item_unchecked_prefix, leaf_block_coverage h]
  rfl

theorem unchecked_nested_refused (n : Nat) (l : Bool) (ts : List Tok) (s : St) :
    item (n + 1) ⟨l, true⟩ (uncheckedInput ts s) =
      .error ⟨0, "nested unchecked block"⟩ := by
  rw [uncheckedInput_eq]
  simp only [item]
  rfl

/-- Yield composition helper. Its premises are actual yield equations;
LeafItems discharges them from the fixed intrinsic leaf constructors. -/
theorem flat_list_yield_cons {c : Cat} (x : Syn c) (xs : Syn (.list c))
    (L : List Choice) (head tail : List Tok)
    (hx : x.yield L = some ([head], L))
    (ht : (xs.yield L).map (fun p => (p.1.flatten, p.2)) = some (tail, L)) :
    ((Syn.cons x xs).yield L).map (fun p => (p.1.flatten, p.2)) =
      some (head ++ tail, L) := by
  rw [Option.map_eq_some_iff] at ht
  obtain ⟨⟨parts, M⟩, hy, he⟩ := ht
  have layouts : M = L := congrArg Prod.snd he
  subst M
  have hc := list_yield_cons_of x xs L L L [head] parts hx hy
  simp only [hc, Option.map_some, List.flatten_cons, List.flatten_nil, List.append_nil]
  have words : parts.flatten = tail := congrArg Prod.fst he
  rw [words]

theorem leaf_items_yield {k : SCtx} {xs : Syn (.list (.item k))} {ts : List Tok}
    (h : LeafItems xs ts) (L : List Choice) :
    (xs.yield L).map (fun p => (p.1.flatten, p.2)) = some (ts, L) := by
  induction h with
  | nil => rfl
  | @returnCons k xs ts h ih =>
    exact flat_list_yield_cons (Syn.stmtItem (k := k) (.returnStmt .none)) xs L
      [.kw .return_, .punct .semi] ts (by rfl) ih
  | @breakCons u xs ts h ih =>
    exact flat_list_yield_cons (Syn.stmtItem (k := ⟨true, u⟩) .breakStmt) xs L
      [.kw .break_, .punct .semi] ts (by rfl) ih
  | @continueCons u xs ts h ih =>
    exact flat_list_yield_cons (Syn.stmtItem (k := ⟨true, u⟩) .continueStmt) xs L
      [.kw .continue_, .punct .semi] ts (by rfl) ih

theorem leaf_block_yield {k : SCtx} {xs : Syn (.list (.item k))} {ts : List Tok}
    (h : LeafItems xs ts) (L : List Choice) :
    (Syn.block xs).yield L = some ([braces ts], L) := by
  obtain ⟨⟨parts, M⟩, hy, he⟩ := Option.map_eq_some_iff.mp (leaf_items_yield h L)
  have layouts : M = L := congrArg Prod.snd he
  subst M
  have hb := block_yield_of_items xs L L parts hy
  have words : parts.flatten = ts := congrArg Prod.fst he
  rw [words] at hb
  exact hb

theorem leaf_block_toks {k : SCtx} {xs : Syn (.list (.item k))} {ts : List Tok}
    (h : LeafItems xs ts) : (Syn.block xs).toks [] = some (braces ts) := by
  unfold Syn.toks
  rw [leaf_block_yield h]
  change Option.some ([braces ts].flatten) = some (braces ts)
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

theorem many_aux_cons_error {α : Type} {p : P (Option α)} {n : Nat} {s mid : St}
    {a : α} {err : Error} (hp : p s = .ok (some a, mid))
    (hr : manyAux p n mid = .error err) : manyAux p (n + 1) s = .error err := by
  simp only [manyAux]
  change (p s).bind (fun z =>
    ((match z.1 with
      | some a => do
        let r ← manyAux p n
        pure (a :: r)
      | none => pure []) : P (List α)) z.2) = _
  rw [hp]
  change (manyAux p n mid).bind (fun q => .ok (a :: q.1, q.2)) = _
  rw [hr]
  rfl

/-- The stopping iteration is necessary: exactly itemCount iterations fail
at the closing brace after consuming every leaf. This is a checked bound,
not a guessed fuel estimate. Internal token offsets are zero. -/
theorem leaf_items_many_underfuel {k : SCtx} {xs : Syn (.list (.item k))} {ts : List Tok}
    (h : LeafItems xs ts) (n : Nat) (s : St) :
    manyAux (blockLeafStep (n + 3) k) (itemCount xs) (leafInput ts s) =
      .error ⟨0, "no progress"⟩ := by
  induction h generalizing n s with
  | nil => simp only [itemCount_nil, itemCount_cons, manyAux]; rfl
  | @returnCons k xs ts hx ih =>
    simp only [itemCount_nil, itemCount_cons]
    change manyAux (blockLeafStep (n + 3) k) (itemCount xs + 1)
      (controlInput (.kw .return_) 0 0 0 0 (leafInput ts s)) = _
    exact many_aux_cons_error (leaf_step_return n k (leafInput ts s)) (ih n s)
  | @breakCons u xs ts hx ih =>
    simp only [itemCount_nil, itemCount_cons]
    change manyAux (blockLeafStep (n + 3) ⟨true, u⟩) (itemCount xs + 1)
      (controlInput (.kw .break_) 0 0 0 0 (leafInput ts s)) = _
    exact many_aux_cons_error (leaf_step_break n u (leafInput ts s)) (ih n s)
  | @continueCons u xs ts hx ih =>
    simp only [itemCount_nil, itemCount_cons]
    change manyAux (blockLeafStep (n + 3) ⟨true, u⟩) (itemCount xs + 1)
      (controlInput (.kw .continue_) 0 0 0 0 (leafInput ts s)) = _
    exact many_aux_cons_error (leaf_step_continue n u (leafInput ts s)) (ih n s)

#print axioms many_aux_cons_error
#print axioms leaf_items_many_underfuel
#print axioms flat_list_yield_cons
#print axioms leaf_items_yield
#print axioms leaf_block_yield
#print axioms leaf_block_toks
#print axioms leaf_items_many
#print axioms blockInput_eq
#print axioms leaf_block_coverage
#print axioms stmt_block_prefix
#print axioms leaf_block_stmt_coverage
#print axioms uncheckedInput_eq
#print axioms item_unchecked_prefix
#print axioms leaf_unchecked_coverage
#print axioms unchecked_nested_refused
#print axioms leaf_items_token_length
#print axioms many_aux_none
#print axioms many_aux_cons
#print axioms leaf_items_many_aux
#print axioms itemsAsList_inverse
#print axioms leaf_step_return
#print axioms leaf_step_break
#print axioms leaf_step_continue
#print axioms leaf_step_stop
end Solidity.Frontend.StatementGrammarH28
