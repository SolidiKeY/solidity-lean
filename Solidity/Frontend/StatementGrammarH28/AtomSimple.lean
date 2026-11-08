import Solidity.Frontend.StatementGrammarH28.AtomConditional

/-! Simple statements over a stated premise on the `simple` parser.

A simple statement (`declVar`, `declTuple`, `exprStmt`) enters only through
the exposed premise `SimpleAtom`: its tokens parse back, by the existing
`simple` parser, to exactly that tree before `;`, at every fuel of at least
the stated budget. Its first token must be one that the statement, item and
block-loop dispatchers send to `simpleStmt` (`simpleHead`). The premise is
proved here only for identifier expression statements; no expression
completeness or expression uniqueness (SOL-EU) is claimed. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- A conservative subset of the tokens that `stmt`, `item` and the block
loop send to `simpleStmt`: no statement keyword, `unchecked`, brace or the
contextual identifier `revert` (its expression statements are `revertExpr`
in `AtomNested`); `else`, `catch` and `;` are excluded too, for the no-else
and no-catch frames and the `for` header's `eat ;`. -/
def simpleHead : Tok → Bool
  | .kw k => !(k == .if_ || k == .for_ || k == .while_ || k == .do_ || k == .continue_ ||
      k == .break_ || k == .try_ || k == .return_ || k == .emit || k == .assembly ||
      k == .unchecked || k == .else_ || k == .catch_)
  | .punct p => !(p == .lbrace || p == .rbrace || p == .semi)
  | .ident x => x != "revert"
  | _ => true

/-- The `simple` parser premise before `;`, with fuel budget `a`. -/
def SimpleAtom (x : Syn .simple) (ss : List Tok) (a : Nat) : Prop :=
  ∀ (n : Nat) (s : St),
    simple (n + a) (locatedInput (ss ++ [.punct .semi]) s) = .ok (x, punctBefore .semi s)

/-- The statement dispatcher sends a `simpleHead` token to `simpleStmt`. -/
theorem stmt_simple_dispatch (m : Nat) (k : SCtx) (t : Tok) (rest : List Tok) (s : St)
    (ht : simpleHead t = true) :
    stmt (m + 1) k (locatedInput (t :: rest) s) = simpleStmt m k (locatedInput (t :: rest) s) := by
  cases t
  all_goals try rfl
  case kw kw => cases kw <;> first | rfl | cases ht
  case punct p => cases p <;> first | rfl | cases ht
  case ident x =>
    simp only [simpleHead, bne_iff_ne, ne_eq] at ht
    rcases k with ⟨l, u⟩
    cases l <;> cases u <;>
      simp! only [stmt, bind, peek, beq_iff_eq, locatedInput, List.map, atToken, List.cons_append, StateT.bind, peekN, List.drop, List.head?_cons, Option.map_some, Except.bind, Option.some.injEq, Tok.ident.injEq, ht, imp_self]

/-- A token list whose first token is a `simpleHead` token. -/
def simpleHeadList : List Tok → Bool
  | t :: _ => simpleHead t
  | [] => false

theorem ident_simple_atom (x : String) : SimpleAtom (.exprStmt (.ident x)) [.ident x] 6 :=
  fun _ _ => rfl

theorem simple_head_cons {ss : List Tok} (h : simpleHeadList ss = true) :
    ∃ t rest, ss = t :: rest ∧ simpleHead t = true := by
  cases ss with
  | nil => cases h
  | cons t rest => exact ⟨t, rest, rfl, h⟩

/-- A simple statement does not start with `else`. -/
theorem simple_no_else {ss : List Tok} (h : simpleHeadList ss = true) (rest : List Tok) (s : St) :
    NoFollowingElse (locatedInput (ss ++ rest) s) := by
  obtain ⟨t, tail, rfl, ht⟩ := simple_head_cons h
  intro bad
  simp only [locatedInput, List.cons_append, List.map_cons, List.head?_cons, Option.map_some,
    atToken, Option.some.injEq] at bad
  subst bad
  cases ht

/-- `eat ;` refuses a simple-statement head. -/
theorem simple_eat_semi {ss : List Tok} (h : simpleHeadList ss = true) (rest : List Tok) (s : St) :
    eat (.punct .semi) (locatedInput (ss ++ rest) s) = .ok (false, locatedInput (ss ++ rest) s) := by
  obtain ⟨t, tail, rfl, ht⟩ := simple_head_cons h
  cases t
  all_goals try rfl
  case punct p => cases p <;> first | rfl | cases ht

/-- `simpleStmt x;` from the premise. -/
theorem simple_stmt_coverage {k : SCtx} {x : Syn .simple} {ss : List Tok} {a : Nat}
    (hx : SimpleAtom x ss a) (hh : simpleHeadList ss = true) (n : Nat) (s : St) :
    stmt (n + (a + 1) + 6) k (locatedInput (ss ++ [.punct .semi]) s) = .ok (.simpleStmt x, s) := by
  obtain ⟨t, tail, rfl, ht⟩ := simple_head_cons hh
  have fuel : n + (a + 1) + 6 = (n + 5 + a + 1) + 1 := by omega
  rw [fuel, List.cons_append, stmt_simple_dispatch _ k t _ s ht, ← List.cons_append]
  change (simple (n + 5 + a) (locatedInput (t :: tail ++ [.punct .semi]) s)).bind
    (fun p => ((do expectP .semi; return Syn.simpleStmt p.1) : P (Syn (.stmt k))) p.2) = _
  rw [hx (n + 5) s]
  rfl

/-- One block-loop step over a simple statement item. -/
theorem simple_item_step {k : SCtx} {x : Syn (.stmt k)} {ss rest : List Tok} {s s' : St} (m : Nat)
    (hh : simpleHeadList ss = true)
    (parse : stmt m k (locatedInput (ss ++ rest) s) = .ok (x, s')) :
    blockLeafStep (m + 1) k (locatedInput (ss ++ rest) s) = .ok (some (.stmtItem x), s') := by
  have lifted : ((stmt m k (locatedInput (ss ++ rest) s)).bind
      (fun p => .ok (Syn.stmtItem p.1, p.2))).bind
      (fun p => .ok (some p.1, p.2)) = .ok (some (.stmtItem x), s') := by
    rw [parse]
    rfl
  obtain ⟨t, tail, rfl, ht⟩ := simple_head_cons hh
  cases t
  all_goals try exact lifted
  case kw kw => cases kw <;> first | exact lifted | cases ht
  case punct p => cases p <;> first | exact lifted | cases ht

#print axioms stmt_simple_dispatch
#print axioms ident_simple_atom
#print axioms simple_no_else
#print axioms simple_eat_semi
#print axioms simple_stmt_coverage
#print axioms simple_item_step

/-- The `for` header before its initialiser decision. -/
theorem for_header_prefix (m : Nat) (l u : Bool) (s : St) :
    stmt (m + 1) ⟨l, u⟩ (locatedInput [.kw .for_, .punct .lparen] s) =
      ((do if ← eat (.punct .semi) then
             let c ← optExprBefore m .semi
             expectP .semi
             let w ← optExprBefore m .rparen
             expectP .rparen
             let b ← stmt m ⟨true, u⟩
             pure (Syn.forStmt (l := l) Syn.none c w b)
           else
             let i ← simple m
             expectP .semi
             let c ← optExprBefore m .semi
             expectP .semi
             let w ← optExprBefore m .rparen
             expectP .rparen
             let b ← stmt m ⟨true, u⟩
             pure (Syn.forStmt (l := l) (Syn.some i) c w b)) : P (Syn (.stmt ⟨l, u⟩))) s := by
  rw [stmt]
  rfl

#print axioms for_header_prefix

end Solidity.Frontend.StatementGrammarH28
