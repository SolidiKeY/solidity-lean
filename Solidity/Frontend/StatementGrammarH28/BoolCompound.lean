import Solidity.Frontend.StatementGrammarH28.NestedCoverage

/-! Concrete Boolean-condition compound coverage using recursive block bodies.
Boolean literals are explicit fixed atoms; no expression uniqueness claim.
General expression-bearing statement coverage remains open. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def boolBefore (b : Bool) (p : Punct) (s : St) : St :=
  locatedInput [.bool b, .punct p] s

def punctBefore (p : Punct) (s : St) : St := locatedInput [.punct p] s

theorem bool_expr_rparen (n : Nat) (b : Bool) (s : St) :
    expr (n + 5) (boolBefore b .rparen s) = .ok (.lit (.bool b), punctBefore .rparen s) := by
  rfl

theorem bool_expr_semi (n : Nat) (b : Bool) (s : St) :
    expr (n + 5) (boolBefore b .semi s) = .ok (.lit (.bool b), punctBefore .semi s) := by
  rfl

def conditionInput (kw : Kw) (b : Bool) (s : St) : St :=
  locatedInput [.kw kw, .punct .lparen, .bool b, .punct .rparen] s

theorem while_bool_prefix (n : Nat) (l u b : Bool) (s : St) :
    stmt (n + 6) ⟨l, u⟩ (conditionInput .while_ b s) =
      (stmt (n + 5) ⟨true, u⟩ s).bind
        (fun p => .ok (Syn.whileStmt (l := l) (.lit (.bool b)) p.1, p.2)) := by
  rw [stmt]
  change (expr (n + 5) (boolBefore b .rparen s)).bind (fun p =>
    ((do expectP .rparen
         let body ← stmt (n + 5) ⟨true, u⟩
         pure (Syn.whileStmt (l := l) (.lit (.bool b)) body)) : P (Syn (.stmt ⟨l, u⟩))) p.2) = _
  rw [bool_expr_rparen]
  rfl

theorem while_bool_block_coverage {l u : Bool} {xs : Syn (.list (.item ⟨true, u⟩))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (n : Nat) (b : Bool) (s : St) :
    stmt (n + d + 6) ⟨l, u⟩ (conditionInput .while_ b (blockInput ts s)) =
      .ok (.whileStmt (.lit (.bool b)) (.blockStmt (.block xs)), s) := by
  rw [while_bool_prefix, nested_block_stmt_coverage h]
  rfl

def doTail (b : Bool) (s : St) : St :=
  locatedInput [.kw .while_, .punct .lparen, .bool b, .punct .rparen, .punct .semi] s

def doInput (ts : List Tok) (b : Bool) (s : St) : St :=
  locatedInput [.kw .do_] (blockInput ts (doTail b s))

theorem do_bool_block_coverage {l u : Bool} {xs : Syn (.list (.item ⟨true, u⟩))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (n : Nat) (b : Bool) (s : St) :
    stmt (n + d + 6) ⟨l, u⟩ (doInput ts b s) =
      .ok (.doWhile (.blockStmt (.block xs)) (.lit (.bool b)), s) := by
  rw [stmt]
  change (stmt (n + d + 5) ⟨true, u⟩ (blockInput ts (doTail b s))).bind (fun p =>
    ((do expect (.kw .while_) "'while'"
         expectP .lparen
         let c ← expr (n + d + 5)
         expectP .rparen
         expectP .semi
         pure (Syn.doWhile (l := l) p.1 c)) : P (Syn (.stmt ⟨l, u⟩))) p.2) = _
  rw [nested_block_stmt_coverage h]
  change (expr (n + d + 5) (boolBefore b .rparen (punctBefore .semi s))).bind (fun p =>
    ((do expectP .rparen
         expectP .semi
         pure (Syn.doWhile (l := l) (.blockStmt (.block xs)) p.1)) :
      P (Syn (.stmt ⟨l, u⟩))) p.2) = _
  rw [bool_expr_rparen]
  rfl

def forEmptyInput (s : St) : St :=
  locatedInput [.kw .for_, .punct .lparen, .punct .semi, .punct .semi, .punct .rparen] s

theorem for_empty_block_coverage {l u : Bool} {xs : Syn (.list (.item ⟨true, u⟩))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (n : Nat) (s : St) :
    stmt (n + d + 6) ⟨l, u⟩ (forEmptyInput (blockInput ts s)) =
      .ok (.forStmt .none .none .none (.blockStmt (.block xs)), s) := by
  rw [stmt]
  change (stmt (n + d + 5) ⟨true, u⟩ (blockInput ts s)).bind
    (fun p => .ok (Syn.forStmt (l := l) .none .none .none p.1, p.2)) = _
  rw [nested_block_stmt_coverage h]
  rfl

/-- Necessary no-else boundary, stated as a token observation rather than
an assumed parser result. -/
def NoFollowingElse (s : St) : Prop := s.ts.head?.map (fun t : Located => t.tok) ≠ some (.kw .else_)

theorem eat_else_false (s : St) (h : NoFollowingElse s) :
    eat (.kw .else_) s = .ok (false, s) := by
  have hb : (s.ts.head?.map (fun t : Located => t.tok) == some (Tok.kw .else_)) = false :=
    beq_eq_false_iff_ne.mpr h
  unfold eat isTok peek peekN
  change (if s.ts.head?.map (fun t : Located => t.tok) == some (Tok.kw .else_) then
    (do advance; pure true) else pure false) s = _
  rw [hb]
  rfl

theorem if_bool_block_none_coverage {k : SCtx} {xs : Syn (.list (.item k))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (n : Nat) (b : Bool) (s : St)
    (he : NoFollowingElse s) :
    stmt (n + d + 6) k (conditionInput .if_ b (blockInput ts s)) =
      .ok (.ifStmt (.lit (.bool b)) (.blockStmt (.block xs)) .none, s) := by
  rw [stmt]
  change (expr (n + d + 5) (boolBefore b .rparen (blockInput ts s))).bind (fun p =>
    ((do expectP .rparen
         let body ← stmt (n + d + 5) k
         if ← eat (.kw .else_) then
           return Syn.ifStmt p.1 body (.some (← stmt (n + d + 5) k))
         else return Syn.ifStmt p.1 body .none) : P (Syn (.stmt k))) p.2) = _
  rw [bool_expr_rparen]
  change (stmt (n + d + 5) k (blockInput ts s)).bind (fun p =>
    ((do if ← eat (.kw .else_) then
           return Syn.ifStmt (.lit (.bool b)) p.1 (.some (← stmt (n + d + 5) k))
         else return Syn.ifStmt (.lit (.bool b)) p.1 .none) : P (Syn (.stmt k))) p.2) = _
  rw [nested_block_stmt_coverage h]
  change (eat (.kw .else_) s).bind (fun p =>
    ((if p.1 then do
        return Syn.ifStmt (.lit (.bool b)) (.blockStmt (.block xs))
          (.some (← stmt (n + d + 5) k))
      else pure (Syn.ifStmt (.lit (.bool b)) (.blockStmt (.block xs)) .none)) :
      P (Syn (.stmt k))) p.2) = _
  rw [eat_else_false s he]
  rfl

def elseInput (ts : List Tok) (s : St) : St :=
  locatedInput [.kw .else_] (blockInput ts s)

theorem if_bool_blocks_some_coverage {k : SCtx}
    {xs ys : Syn (.list (.item k))} {ts us : List Tok} {d e : Nat}
    (hx : NestedItems xs ts d) (hy : NestedItems ys us e) (n : Nat) (b : Bool) (s : St) :
    stmt (n + d + e + 6) k (conditionInput .if_ b (blockInput ts (elseInput us s))) =
      .ok (.ifStmt (.lit (.bool b)) (.blockStmt (.block xs))
        (.some (.blockStmt (.block ys))), s) := by
  have hb := nested_block_stmt_coverage hx (n + e) (elseInput us s)
  have fuel : n + e + d + 5 = n + d + e + 5 := by omega
  rw [fuel] at hb
  rw [stmt]
  change (expr (n + d + e + 5) (boolBefore b .rparen
    (blockInput ts (elseInput us s)))).bind (fun p =>
    ((do expectP .rparen
         let body ← stmt (n + d + e + 5) k
         if ← eat (.kw .else_) then
           return Syn.ifStmt p.1 body (.some (← stmt (n + d + e + 5) k))
         else return Syn.ifStmt p.1 body .none) : P (Syn (.stmt k))) p.2) = _
  rw [bool_expr_rparen]
  change (stmt (n + d + e + 5) k (blockInput ts (elseInput us s))).bind (fun p =>
    ((do if ← eat (.kw .else_) then
           return Syn.ifStmt (.lit (.bool b)) p.1 (.some (← stmt (n + d + e + 5) k))
         else return Syn.ifStmt (.lit (.bool b)) p.1 .none) : P (Syn (.stmt k))) p.2) = _
  rw [hb]
  change (stmt (n + d + e + 5) k (blockInput us s)).bind
    (fun p => .ok (Syn.ifStmt (.lit (.bool b)) (.blockStmt (.block xs)) (.some p.1), p.2)) = _
  rw [nested_block_stmt_coverage hy]
  rfl

theorem while_bool_block_yield {l u : Bool} {xs : Syn (.list (.item ⟨true, u⟩))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (b : Bool) (L : List Choice) :
    (Syn.whileStmt (l := l) (.lit (.bool b)) (.blockStmt (.block xs))).yield L =
      some ([tk .while_ ++ parens [.bool b] ++ braces ts], L) := by
  rw [Syn.yield]
  change ((Syn.block xs).yield L).bind (fun p =>
    some ([tk .while_ ++ parens [.bool b] ++ p.1.flatten], p.2)) = _
  rw [nested_block_yield h L]
  simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem do_bool_block_yield {l u : Bool} {xs : Syn (.list (.item ⟨true, u⟩))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (b : Bool) (L : List Choice) :
    (Syn.doWhile (l := l) (.blockStmt (.block xs)) (.lit (.bool b))).yield L =
      some ([tk .do_ ++ braces ts ++ tk .while_ ++ parens [.bool b] ++ pu .semi], L) := by
  rw [Syn.yield]
  change ((Syn.block xs).yield L).bind (fun p =>
    some ([tk .do_ ++ p.1.flatten ++ tk .while_ ++ parens [.bool b] ++ pu .semi], p.2)) = _
  rw [nested_block_yield h L]
  simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem for_empty_block_yield {l u : Bool} {xs : Syn (.list (.item ⟨true, u⟩))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (L : List Choice) :
    (Syn.forStmt (l := l) .none .none .none (.blockStmt (.block xs))).yield L =
      some ([tk .for_ ++ parens (pu .semi ++ pu .semi) ++ braces ts], L) := by
  rw [Syn.yield]
  change ((Syn.block xs).yield L).bind (fun p =>
    some ([tk .for_ ++ parens (pu .semi ++ pu .semi) ++ p.1.flatten], p.2)) = _
  rw [nested_block_yield h L]
  simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem if_bool_block_none_yield {k : SCtx} {xs : Syn (.list (.item k))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (b : Bool) (L : List Choice) :
    (Syn.ifStmt (.lit (.bool b)) (.blockStmt (.block xs)) .none).yield L =
      some ([tk .if_ ++ parens [.bool b] ++ braces ts], L) := by
  rw [Syn.yield]
  change ((Syn.block xs).yield L).bind (fun p =>
    some ([tk .if_ ++ parens [.bool b] ++ p.1.flatten ++ []], p.2)) = _
  rw [nested_block_yield h L]
  simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem some_nested_stmt_yield {k : SCtx} {xs : Syn (.list (.item k))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (L : List Choice) :
    (Syn.some (Syn.blockStmt (Syn.block xs))).yield L = some ([braces ts], L) := by
  rw [Syn.yield]
  change ((Syn.block xs).yield L).bind (fun p => some ([p.1.flatten], p.2)) = _
  rw [nested_block_yield h L]
  simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem if_bool_blocks_some_yield {k : SCtx}
    {xs ys : Syn (.list (.item k))} {ts us : List Tok} {d e : Nat}
    (hx : NestedItems xs ts d) (hy : NestedItems ys us e) (b : Bool) (L : List Choice) :
    (Syn.ifStmt (.lit (.bool b)) (.blockStmt (.block xs))
      (.some (.blockStmt (.block ys)))).yield L =
      some ([tk .if_ ++ parens [.bool b] ++ braces ts ++ tk .else_ ++ braces us], L) := by
  rw [Syn.yield]
  change ((Syn.block xs).yield L).bind (fun p =>
    ((Syn.some (Syn.blockStmt (Syn.block ys))).yield p.2).bind (fun q =>
      some ([tk .if_ ++ parens [.bool b] ++ p.1.flatten ++
        (match q.1 with | [s] => tk .else_ ++ s | _ => [])], q.2))) = _
  rw [nested_block_yield hx L]
  change ((Syn.some (Syn.blockStmt (Syn.block ys))).yield L).bind (fun q =>
      some ([tk .if_ ++ parens [.bool b] ++ [braces ts].flatten ++
        (match q.1 with | [s] => tk .else_ ++ s | _ => [])], q.2)) = _
  rw [some_nested_stmt_yield hy L]
  simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.append_assoc]

#print axioms some_nested_stmt_yield
#print axioms if_bool_blocks_some_yield
#print axioms while_bool_block_yield
#print axioms do_bool_block_yield
#print axioms for_empty_block_yield
#print axioms if_bool_block_none_yield
#print axioms eat_else_false
#print axioms if_bool_block_none_coverage
#print axioms if_bool_blocks_some_coverage
#print axioms do_bool_block_coverage
#print axioms for_empty_block_coverage
#print axioms while_bool_prefix
#print axioms while_bool_block_coverage
#print axioms bool_expr_rparen
#print axioms bool_expr_semi
end Solidity.Frontend.StatementGrammarH28
