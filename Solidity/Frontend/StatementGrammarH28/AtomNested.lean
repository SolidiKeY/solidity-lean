import Solidity.Frontend.StatementGrammarH28.AtomAsm
import Solidity.Frontend.StatementGrammarH28.G0Nodes

/-! Arbitrarily nested statements and item lists over expression atoms.

`AtomStmt`, `AtomItems`, `AtomCatch` and `AtomCatches` are mutual relations
over the existing indexed syntax (no alternate AST): blocks of arbitrary
width and depth, empty return, break and continue in their intrinsic
contexts, `return e;`, `unchecked` items in their permitted context,
`if`/`while`/`do` with atom conditions, `for` with an optional simple
initialiser and optional atom condition and update (`OptAtom`), simple
statements, `emit`/`revert`, contextual `revert` expression statements
(`revertExpr`), `try` with or without `returns` and any number of plain or
signature catch clauses, and `assembly`. Sub-trees outside the statement
grammar enter only through exposed premises on their own sub-parsers
(`ExprAtomRparen`, `ExprAtomSemi`, `SimpleAtom`, `PathAtom`, `ArgsAtom`,
`ExprAtomBrace`, `ExprAtomReturns`, `RetsAtom`, `ParamsAtom`, `YulBodyAtom`,
`FlagsAtom`); expression parser completeness and expression uniqueness
(SOL-EU) are not claimed. The else-bearing constructor keeps exactly the
existing closed-then contract. Coverage takes the existing else frame and
the catch frame `CatchFrame` (only a catch-open statement, whose last
sub-statement is a `try`, needs a following token other than `catch`). All
parser success is derived by mutual structural recursion on the witness,
with a budget computed from the syntax; no successful parse is assumed. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- Exposed expression-atom premise before `;`, with fuel budget `a`. -/
def ExprAtomSemi (e : Syn .expr) (es : List Tok) (a : Nat) : Prop :=
  ∀ (n : Nat) (s : St),
    expr (n + a) (locatedInput (es ++ [.punct .semi]) s) = .ok (e, punctBefore .semi s)

/-- The atom is nonempty and does not start with the terminator
(`return;` is the empty return). -/
def NoSemiHead (es : List Tok) : Prop := es ≠ [] ∧ es.head? ≠ some (.punct .semi)

theorem bool_atom_semi (b : Bool) : ExprAtomSemi (.lit (.bool b)) [.bool b] 5 :=
  fun n s => bool_expr_semi n b s

theorem ident_atom_semi (x : String) : ExprAtomSemi (.ident x) [.ident x] 5 :=
  fun _ _ => rfl

/-- An optional expression atom before the punctuation `p` (a `for` header's
condition before `;` or update before `)`): absent with no tokens, or present
under the exposed atom premise with a nonempty token list not starting with `p`. -/
inductive OptAtom (p : Punct) : Syn (.opt .expr) → List Tok → Nat → Prop where
  | none : OptAtom p .none [] 0
  | some {e : Syn .expr} {es : List Tok} {a : Nat} :
      (∀ (n : Nat) (s : St),
        expr (n + a) (locatedInput (es ++ [.punct p]) s) = .ok (e, punctBefore p s)) →
      es ≠ [] → es.head? ≠ some (.punct p) → OptAtom p (.some e) es a

theorem isP_false_of_head {p : Punct} {es : List Tok} (hn : es ≠ [])
    (hh : es.head? ≠ some (.punct p)) (rest : List Tok) (s : St) :
    isP p (locatedInput (es ++ rest) s) = .ok (false, locatedInput (es ++ rest) s) := by
  have hb : ((locatedInput (es ++ rest) s).ts.head?.map
      (fun t : Located => t.tok) == some (Tok.punct p)) = false := by
    cases es with
    | nil => exact absurd rfl hn
    | cons t tail =>
      apply beq_eq_false_iff_ne.mpr
      intro bad
      apply hh
      simp only [locatedInput, List.cons_append, List.map_cons, List.head?_cons,
        Option.map_some, atToken] at bad
      simp only [List.head?_cons, bad]
  unfold isP isTok peek peekN
  change (pure ((locatedInput (es ++ rest) s).ts.head?.map
    (fun t : Located => t.tok) == some (Tok.punct p)) : P Bool) _ = _
  rw [hb]
  rfl

/-- The optional-expression parser on an optional atom. -/
theorem opt_atom_coverage {p : Punct} {c : Syn (.opt .expr)} {cs : List Tok} {a : Nat}
    (h : OptAtom p c cs a) (n : Nat) (s : St) :
    optExprBefore (n + a + 1) p (locatedInput (cs ++ [.punct p]) s) = .ok (c, punctBefore p s) := by
  cases h with
  | none =>
    simp only [optExprBefore]
    change (isP p (punctBefore p s)).bind (fun q =>
      ((if q.1 then pure Syn.none else do return Syn.some (← expr (n + 0))) :
        P (Syn (.opt .expr))) q.2) = _
    have hp : isP p (punctBefore p s) = .ok (true, punctBefore p s) := by
      unfold isP isTok peek peekN
      change (pure ((punctBefore p s).ts.head?.map
        (fun t : Located => t.tok) == some (Tok.punct p)) : P Bool) _ = _
      simp only [punctBefore, locatedInput, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, List.head?_cons, Option.map_some, atToken, beq_self_eq_true]
      rfl
    rw [hp]
    rfl
  | some he hn hh =>
    simp only [optExprBefore]
    change (isP p (locatedInput (cs ++ [.punct p]) s)).bind (fun q =>
      ((if q.1 then pure Syn.none else do return Syn.some (← expr (n + a))) :
        P (Syn (.opt .expr))) q.2) = _
    rw [isP_false_of_head hn hh]
    change (expr (n + a) (locatedInput (cs ++ [.punct p]) s)).bind
      (fun q => .ok (Syn.some q.1, q.2)) = _
    rw [he n s]
    rfl

mutual
inductive AtomStmt : {k : SCtx} → Syn (.stmt k) → List Tok → Nat → Prop where
  | block {k : SCtx} {xs : Syn (.list (.item k))} {parts : List (List Tok)} {b : Nat} :
      AtomItems xs parts b → AtomStmt (.blockStmt (.block xs)) (braces parts.flatten) b
  | returnNone {k : SCtx} :
      AtomStmt (k := k) (.returnStmt .none) [.kw .return_, .punct .semi] 0
  | returnSome {k : SCtx} {e : Syn .expr} {es : List Tok} {a : Nat} :
      ExprAtomSemi e es a → NoSemiHead es →
      AtomStmt (k := k) (.returnStmt (.some e)) ([.kw .return_] ++ es ++ [.punct .semi]) (a + 1)
  | breakStmt {u : Bool} : AtomStmt (k := ⟨true, u⟩) .breakStmt [.kw .break_, .punct .semi] 0
  | continueStmt {u : Bool} :
      AtomStmt (k := ⟨true, u⟩) .continueStmt [.kw .continue_, .punct .semi] 0
  | ifNone {k : SCtx} {c : Syn .expr} {cs : List Tok} {a : Nat}
      {x : Syn (.stmt k)} {ts : List Tok} {d : Nat} :
      ExprAtomRparen c cs a → AtomStmt x ts d →
      AtomStmt (.ifStmt c x .none)
        ([.kw .if_, .punct .lparen] ++ cs ++ [.punct .rparen] ++ ts) (d + a + 1)
  | ifSome {k : SCtx} {c : Syn .expr} {cs : List Tok} {a : Nat}
      {t e : Syn (.stmt k)} {ts es : List Tok} {d f : Nat} :
      ExprAtomRparen c cs a → AtomStmt t ts d → AtomStmt e es f → t.openIf = false →
      AtomStmt (.ifStmt c t (.some e))
        ([.kw .if_, .punct .lparen] ++ cs ++ [.punct .rparen] ++ ts ++ [.kw .else_] ++ es)
        (d + f + a + 1)
  | whileLoop {l u : Bool} {c : Syn .expr} {cs : List Tok} {a : Nat}
      {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} {d : Nat} :
      ExprAtomRparen c cs a → AtomStmt x ts d →
      AtomStmt (Syn.whileStmt (l := l) c x)
        ([.kw .while_, .punct .lparen] ++ cs ++ [.punct .rparen] ++ ts) (d + a + 1)
  | forLoop {l u : Bool} {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} {d : Nat} :
      AtomStmt x ts d → AtomStmt (Syn.forStmt (l := l) .none .none .none x)
        ([.kw .for_, .punct .lparen, .punct .semi, .punct .semi, .punct .rparen] ++ ts) (d + 1)
  | doLoop {l u : Bool} {c : Syn .expr} {cs : List Tok} {a : Nat}
      {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} {d : Nat} :
      ExprAtomRparen c cs a → AtomStmt x ts d →
      AtomStmt (Syn.doWhile (l := l) x c)
        ([.kw .do_] ++ ts ++ [.kw .while_, .punct .lparen] ++ cs ++ [.punct .rparen, .punct .semi])
        (d + a + 1)
  | forAtom {l u : Bool} {c v : Syn (.opt .expr)} {cs vs : List Tok} {ca va : Nat}
      {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} {d : Nat} :
      OptAtom .semi c cs ca → OptAtom .rparen v vs va → AtomStmt x ts d →
      AtomStmt (Syn.forStmt (l := l) .none c v x)
        ([.kw .for_, .punct .lparen, .punct .semi] ++ cs ++ [.punct .semi] ++ vs ++
          [.punct .rparen] ++ ts) (d + ca + va + 1)
  | simpleS {k : SCtx} {x : Syn .simple} {ss : List Tok} {a : Nat} :
      SimpleAtom x ss a → simpleHeadList ss = true →
      AtomStmt (k := k) (.simpleStmt x) (ss ++ [.punct .semi]) (a + 1)
  | forInit {l u : Bool} {x : Syn .simple} {ss : List Tok} {a : Nat}
      {c v : Syn (.opt .expr)} {cs vs : List Tok} {ca va : Nat}
      {b : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} {d : Nat} :
      SimpleAtom x ss a → simpleHeadList ss = true →
      OptAtom .semi c cs ca → OptAtom .rparen v vs va → AtomStmt b ts d →
      AtomStmt (Syn.forStmt (l := l) (.some x) c v b)
        ([.kw .for_, .punct .lparen] ++ ss ++ [.punct .semi] ++ cs ++ [.punct .semi] ++ vs ++
          [.punct .rparen] ++ ts) (d + a + ca + va + 1)
  | emitS {k : SCtx} {e : Syn .expr} {ps : List Tok} {args : Syn .callArgs} {as : List Tok}
      {b : Nat} :
      PathAtom e ps → ArgsAtom args as b → as.head? = some (.punct .lparen) →
      e.isPathExpr = true →
      AtomStmt (k := k) (.emit e args) ([.kw .emit] ++ ps ++ as ++ [.punct .semi]) b
  | revertS {k : SCtx} {e : Syn .expr} {y : String} {ps : List Tok} {args : Syn .callArgs}
      {as : List Tok} {b : Nat} :
      PathAtom e (.ident y :: ps) → ArgsAtom args as b → as.head? = some (.punct .lparen) →
      e.isPathExpr = true →
      AtomStmt (k := k) (.revert e args)
        ([.ident "revert"] ++ (.ident y :: ps) ++ as ++ [.punct .semi]) b

  | revertExpr {k : SCtx} {x : Syn .simple} {ss : List Tok} {a : Nat} :
      SimpleAtom x (.ident "revert" :: ss) a → revertExprNext (ss ++ [.punct .semi]) = true →
      AtomStmt (k := k) (.simpleStmt x) (.ident "revert" :: ss ++ [.punct .semi]) (a + 1)
  | asm {k : SCtx} {evm : Bool} {flags : List String} {fts : List Tok}
      {body : Syn (.list .yulStmt)} {ys : List Tok} {a : Nat} :
      AsmFlags flags fts → YulBodyAtom body ys a → ys.head? = some (.punct .lbrace) →
      AtomStmt (k := k) (.assembly evm flags body) ([.kw .assembly] ++ evmToks evm ++ fts ++ ys)
        (a + 1)
  | tryS {k : SCtx} {e : Syn .expr} {es : List Tok} {a : Nat}
      {xs : Syn (.list (.item k))} {parts : List (List Tok)} {b : Nat}
      {c : Syn (.catchClause k)} {cts : List Tok} {f : Nat}
      {cs : Syn (.list (.catchClause k))} {cparts : List (List Tok)} {g : Nat} :
      ExprAtomBrace e es a → AtomItems xs parts b → BlockBodyParts parts →
      AtomCatch c cts f → AtomCatches cs cparts g →
      AtomStmt (.tryStmt e .nil (.block xs) c cs)
        ([.kw .try_] ++ es ++ braces parts.flatten ++ cts ++ cparts.flatten) (a + b + f + g + 2)
  | tryRets {k : SCtx} {e : Syn .expr} {es : List Tok} {a : Nat}
      {rets : Syn (.list .param)} {rs : List Tok} {r : Nat}
      {xs : Syn (.list (.item k))} {parts : List (List Tok)} {b : Nat}
      {c : Syn (.catchClause k)} {cts : List Tok} {f : Nat}
      {cs : Syn (.list (.catchClause k))} {cparts : List (List Tok)} {g : Nat} :
      ExprAtomReturns e es a → RetsAtom rets (.kw .returns :: rs) r → AtomItems xs parts b →
      AtomCatch c cts f → AtomCatches cs cparts g →
      AtomStmt (.tryStmt e rets (.block xs) c cs)
        ([.kw .try_] ++ es ++ (.kw .returns :: rs) ++ braces parts.flatten ++ cts ++
          cparts.flatten) (a + r + b + f + g + 2)

inductive AtomItems : {k : SCtx} → Syn (.list (.item k)) → List (List Tok) → Nat → Prop where
  | nil {k : SCtx} : AtomItems (Syn.nil (c := .item k)) [] 0
  | stmtCons {k : SCtx} {x : Syn (.stmt k)} {xs : Syn (.list (.item k))}
      {ts : List Tok} {parts : List (List Tok)} {d b : Nat} :
      AtomStmt x ts d → AtomItems xs parts b →
      AtomItems (.cons (.stmtItem x) xs) (ts :: parts) (max (d + 7) b)
  | uncheckedCons {l : Bool} {ys : Syn (.list (.item ⟨l, true⟩))}
      {xs : Syn (.list (.item ⟨l, false⟩))} {qs parts : List (List Tok)} {c b : Nat} :
      AtomItems ys qs c → AtomItems xs parts b →
      AtomItems (.cons (.uncheckedItem (.block ys)) xs)
        ((.kw .unchecked :: braces qs.flatten) :: parts) (max (c + 2) b)

/-- Catch clauses with item-list bodies; signature parameters enter through
the exposed `ParamsAtom` premise. -/
inductive AtomCatch : {k : SCtx} → Syn (.catchClause k) → List Tok → Nat → Prop where
  | plain {k : SCtx} {xs : Syn (.list (.item k))} {parts : List (List Tok)} {b : Nat} :
      AtomItems xs parts b →
      AtomCatch (.catchPlain (.block xs)) ([.kw .catch_] ++ braces parts.flatten) (b + 2)
  | sig {k : SCtx} {name : Option String} {p : Syn .param} {ps : Syn (.list .param)}
      {pts : List Tok} {a : Nat} {xs : Syn (.list (.item k))} {parts : List (List Tok)}
      {b : Nat} :
      ParamsAtom (.cons p ps) pts a → pts.head? = some (.punct .lparen) → AtomItems xs parts b →
      AtomCatch (.catchSig name p ps (.block xs))
        ([.kw .catch_] ++ optToks idt name ++ pts ++ braces parts.flatten) (a + b + 2)

inductive AtomCatches : {k : SCtx} → Syn (.list (.catchClause k)) → List (List Tok) → Nat →
    Prop where
  | nil {k : SCtx} : AtomCatches (Syn.nil (c := .catchClause k)) [] 0
  | cons {k : SCtx} {c : Syn (.catchClause k)} {cs : Syn (.list (.catchClause k))}
      {ts : List Tok} {parts : List (List Tok)} {d b : Nat} :
      AtomCatch c ts d → AtomCatches cs parts b → AtomCatches (.cons c cs) (ts :: parts) (max d b)
end

theorem atom_catch_head {k : SCtx} {c : Syn (.catchClause k)} {ts : List Tok} {d : Nat}
    (h : AtomCatch c ts d) : ts.head? = some (.kw .catch_) := by
  cases h <;> rfl

theorem atom_catches_count_le : {k : SCtx} → {cs : Syn (.list (.catchClause k))} →
    {parts : List (List Tok)} → {b : Nat} → AtomCatches cs parts b →
    g0ListLength cs ≤ parts.flatten.length
  | _, _, _, _, .nil => Nat.le_refl 0
  | _, _, _, _, .cons (ts := ts) hc ht => by
    have hn : ts.length ≠ 0 := by
      intro zero
      have hh := atom_catch_head hc
      rw [List.eq_nil_of_length_eq_zero zero] at hh
      cases hh
    have ih := atom_catches_count_le ht
    simp only [g0ListLength_cons, List.flatten_cons, List.length_append]
    omega

/-- No atom statement starts with `else`. -/
theorem atom_stmt_no_else_input {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok} {d : Nat}
    (h : AtomStmt x ts d) (s : St) : NoFollowingElse (locatedInput ts s) := by
  cases h
  case simpleS _ hh => exact simple_no_else hh _ s
  all_goals (intro bad; cases bad)

theorem atom_stmt_tokens_nonempty {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok} {d : Nat}
    (h : AtomStmt x ts d) : ts ≠ [] := by
  intro he
  subst ts
  exact atom_stmt_no_else_input h (locatedInput [.kw .else_] ⟨[], [], 0⟩) rfl

theorem atom_items_no_else {k : SCtx} {xs : Syn (.list (.item k))} {parts : List (List Tok)}
    {b : Nat} (h : AtomItems xs parts b) (s : St) (hs : NoFollowingElse s) :
    NoFollowingElse (locatedInput parts.flatten s) := by
  cases h with
  | nil => exact hs
  | stmtCons hx _ =>
    rw [List.flatten_cons, locatedInput_append]
    exact atom_stmt_no_else_input hx _
  | uncheckedCons => intro bad; cases bad

/-- No atom statement starts with `catch`. -/
theorem atom_stmt_no_catch_input {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok} {d : Nat}
    (h : AtomStmt x ts d) (s : St) : NoFollowingCatch (locatedInput ts s) := by
  cases h
  case simpleS _ hh =>
    obtain ⟨t, tail, rfl, ht⟩ := simple_head_cons hh
    intro bad
    simp only [locatedInput, List.cons_append, List.map_cons, List.head?_cons, Option.map_some,
      atToken, Option.some.injEq] at bad
    subst bad
    cases ht
  all_goals (intro bad; cases bad)

theorem atom_items_no_catch {k : SCtx} {xs : Syn (.list (.item k))} {parts : List (List Tok)}
    {b : Nat} (h : AtomItems xs parts b) (s : St) (hs : NoFollowingCatch s) :
    NoFollowingCatch (locatedInput parts.flatten s) := by
  cases h with
  | nil => exact hs
  | stmtCons hx _ =>
    rw [List.flatten_cons, locatedInput_append]
    exact atom_stmt_no_catch_input hx _
  | uncheckedCons => intro bad; cases bad

theorem atom_items_count_le : {k : SCtx} → {xs : Syn (.list (.item k))} →
    {parts : List (List Tok)} → {b : Nat} → AtomItems xs parts b →
    itemCount xs ≤ parts.flatten.length
  | _, _, _, _, .nil => Nat.le_refl 0
  | _, _, _, _, .stmtCons (ts := ts) hx ht => by
    have hn : ts.length ≠ 0 := by
      intro zero
      exact atom_stmt_tokens_nonempty hx (List.eq_nil_of_length_eq_zero zero)
    have ih := atom_items_count_le ht
    simp only [itemCount_cons, List.flatten_cons, List.length_append]
    omega
  | _, _, _, _, .uncheckedCons _ ht => by
    have ih := atom_items_count_le ht
    simp only [itemCount_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

/-- One loop step of the block parser over a represented statement item. -/
theorem atom_item_step {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok} {d : Nat}
    (h : AtomStmt x ts d) (m : Nat) (s : St)
    (parse : stmt m k (locatedInput ts s) = .ok (x, s)) :
    blockLeafStep (m + 1) k (locatedInput ts s) = .ok (some (.stmtItem x), s) := by
  have lifted : ((stmt m k (locatedInput ts s)).bind
      (fun p => .ok (Syn.stmtItem p.1, p.2))).bind
      (fun p => .ok (some p.1, p.2)) = .ok (some (.stmtItem x), s) := by
    rw [parse]
    rfl
  cases h
  case simpleS _ hh => exact simple_item_step m hh parse
  all_goals
    simp only [blockLeafStep, item, braces, pu, List.cons_append, List.nil_append,
      List.append_assoc] at lifted ⊢
    exact lifted

theorem atom_empty_return (n : Nat) (k : SCtx) (s : St) :
    stmt (n + 0 + 6) k (locatedInput [.kw .return_, .punct .semi] s) = .ok (.returnStmt .none, s) :=
  empty_return_coverage (n + 4) k 0 0 0 0 s

theorem atom_return_some {k : SCtx} {e : Syn .expr} {es : List Tok} {a : Nat}
    (he : ExprAtomSemi e es a) (hs : NoSemiHead es) (n : Nat) (s : St) :
    stmt (n + (a + 1) + 6) k (locatedInput ([.kw .return_] ++ es ++ [.punct .semi]) s) =
      .ok (.returnStmt (.some e), s) := by
  have fuel : n + (a + 1) + 6 = ((n + 5 + a) + 1) + 1 := by omega
  have hi : locatedInput ([.kw .return_] ++ es ++ [.punct .semi]) s =
      locatedInput [.kw .return_] (locatedInput (es ++ [.punct .semi]) s) := by
    simp only [← locatedInput_append, List.cons_append, List.nil_append]
  rw [fuel, hi, stmt]
  change (optExprBefore (n + 5 + a + 1) .semi (locatedInput (es ++ [.punct .semi]) s)).bind
    (fun p => ((do expectP .semi; return Syn.returnStmt p.1) : P (Syn (.stmt k))) p.2) = _
  have hopt : optExprBefore (n + 5 + a + 1) .semi (locatedInput (es ++ [.punct .semi]) s) =
      .ok (.some e, punctBefore .semi s) := by
    have hp : isP .semi (locatedInput (es ++ [.punct .semi]) s) =
        .ok (false, locatedInput (es ++ [.punct .semi]) s) := by
      have hb : ((locatedInput (es ++ [.punct .semi]) s).ts.head?.map
          (fun t : Located => t.tok) == some (Tok.punct .semi)) = false := by
        cases es with
        | nil => exact absurd rfl hs.1
        | cons t rest =>
          apply beq_eq_false_iff_ne.mpr
          intro bad
          apply hs.2
          simp only [locatedInput, List.cons_append, List.map_cons, List.head?_cons,
            Option.map_some, atToken] at bad
          simp only [List.head?_cons, bad]
      unfold isP isTok peek peekN
      change (pure ((locatedInput (es ++ [.punct .semi]) s).ts.head?.map
        (fun t : Located => t.tok) == some (Tok.punct .semi)) : P Bool) _ = _
      rw [hb]
      rfl
    simp only [optExprBefore]
    change (isP .semi (locatedInput (es ++ [.punct .semi]) s)).bind (fun p =>
      ((if p.1 then pure Syn.none else do return Syn.some (← expr (n + 5 + a))) :
        P (Syn (.opt .expr))) p.2) = _
    rw [hp]
    change (expr (n + 5 + a) (locatedInput (es ++ [.punct .semi]) s)).bind
      (fun p => .ok (Syn.some p.1, p.2)) = _
    rw [he (n + 5) s]
    rfl
  rw [hopt]
  rfl

/-- The `for` header with an empty initialiser, before its optional parts. -/
theorem for_empty_init_prefix (m : Nat) (l u : Bool) (s : St) :
    stmt (m + 1) ⟨l, u⟩ (locatedInput [.kw .for_, .punct .lparen, .punct .semi] s) =
      ((do let c ← optExprBefore m .semi
           expectP .semi
           let w ← optExprBefore m .rparen
           expectP .rparen
           let b ← stmt m ⟨true, u⟩
           pure (Syn.forStmt (l := l) Syn.none c w b)) : P (Syn (.stmt ⟨l, u⟩))) s := by
  rw [stmt]
  rfl

/-- One `for` statement with optional atom condition and update, given its body. -/
theorem for_atom_step {u : Bool} {c v : Syn (.opt .expr)} {cs vs : List Tok} {ca va : Nat}
    (hc : OptAtom .semi c cs ca) (hv : OptAtom .rparen v vs va) (m : Nat) (l : Bool)
    {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} (s : St)
    (hb : stmt (m + ca + va + 5) ⟨true, u⟩ (locatedInput ts s) = .ok (x, s)) :
    stmt (m + ca + va + 5 + 1) ⟨l, u⟩
      (locatedInput ([.kw .for_, .punct .lparen, .punct .semi] ++ cs ++ [.punct .semi] ++ vs ++
        [.punct .rparen] ++ ts) s) = .ok (Syn.forStmt (l := l) .none c v x, s) := by
  have hcv := opt_atom_coverage hc (m + va + 4)
    (locatedInput (vs ++ [.punct .rparen]) (locatedInput ts s))
  rw [show m + va + 4 + ca + 1 = m + ca + va + 5 by omega] at hcv
  have hvv := opt_atom_coverage hv (m + ca + 4) (locatedInput ts s)
  rw [show m + ca + 4 + va + 1 = m + ca + va + 5 by omega] at hvv
  have hi : locatedInput ([.kw .for_, .punct .lparen, .punct .semi] ++ cs ++ [.punct .semi] ++
      vs ++ [.punct .rparen] ++ ts) s =
      locatedInput [.kw .for_, .punct .lparen, .punct .semi]
        (locatedInput (cs ++ [.punct .semi]) (locatedInput (vs ++ [.punct .rparen])
          (locatedInput ts s))) := by
    simp only [← locatedInput_append, List.append_assoc]
  rw [hi, for_empty_init_prefix]
  generalize m + ca + va + 5 = M at hcv hvv hb ⊢
  change (optExprBefore M .semi
      (locatedInput (cs ++ [.punct .semi]) (locatedInput (vs ++ [.punct .rparen])
        (locatedInput ts s)))).bind (fun p =>
    ((do expectP .semi
         let w ← optExprBefore M .rparen
         expectP .rparen
         let b ← stmt M ⟨true, u⟩
         pure (Syn.forStmt (l := l) Syn.none p.1 w b)) : P (Syn (.stmt ⟨l, u⟩))) p.2) = _
  rw [hcv]
  change (optExprBefore M .rparen (locatedInput (vs ++ [.punct .rparen]) (locatedInput ts s))).bind
    (fun p => ((do expectP .rparen
                   let b ← stmt M ⟨true, u⟩
                   pure (Syn.forStmt (l := l) Syn.none c p.1 b)) :
      P (Syn (.stmt ⟨l, u⟩))) p.2) = _
  rw [hvv]
  change (stmt M ⟨true, u⟩ (locatedInput ts s)).bind
    (fun p => .ok (Syn.forStmt (l := l) Syn.none c v p.1, p.2)) = _
  rw [hb]
  rfl

/-- One `for` statement with a simple-statement initialiser and optional atom
condition and update, given its body. -/
theorem for_init_step {u : Bool} {x : Syn .simple} {ss : List Tok} {a : Nat}
    {c v : Syn (.opt .expr)} {cs vs : List Tok} {ca va : Nat}
    (hx : SimpleAtom x ss a) (hh : simpleHeadList ss = true)
    (hc : OptAtom .semi c cs ca) (hv : OptAtom .rparen v vs va) (m : Nat) (l : Bool)
    {b : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} (s : St)
    (hb : stmt (m + a + ca + va + 5) ⟨true, u⟩ (locatedInput ts s) = .ok (b, s)) :
    stmt (m + a + ca + va + 5 + 1) ⟨l, u⟩
      (locatedInput ([.kw .for_, .punct .lparen] ++ ss ++ [.punct .semi] ++ cs ++
        [.punct .semi] ++ vs ++ [.punct .rparen] ++ ts) s) =
      .ok (Syn.forStmt (l := l) (.some x) c v b, s) := by
  have hsx := hx (m + ca + va + 5) (locatedInput (cs ++ [.punct .semi])
    (locatedInput (vs ++ [.punct .rparen]) (locatedInput ts s)))
  rw [show m + ca + va + 5 + a = m + a + ca + va + 5 by omega] at hsx
  have hcv := opt_atom_coverage hc (m + a + va + 4)
    (locatedInput (vs ++ [.punct .rparen]) (locatedInput ts s))
  rw [show m + a + va + 4 + ca + 1 = m + a + ca + va + 5 by omega] at hcv
  have hvv := opt_atom_coverage hv (m + a + ca + 4) (locatedInput ts s)
  rw [show m + a + ca + 4 + va + 1 = m + a + ca + va + 5 by omega] at hvv
  have hi : locatedInput ([.kw .for_, .punct .lparen] ++ ss ++ [.punct .semi] ++ cs ++
      [.punct .semi] ++ vs ++ [.punct .rparen] ++ ts) s =
      locatedInput [.kw .for_, .punct .lparen] (locatedInput (ss ++ [.punct .semi])
        (locatedInput (cs ++ [.punct .semi]) (locatedInput (vs ++ [.punct .rparen])
          (locatedInput ts s)))) := by
    simp only [← locatedInput_append, List.append_assoc]
  rw [hi, for_header_prefix]
  generalize m + a + ca + va + 5 = M at hsx hcv hvv hb ⊢
  simp only [bind, StateT.bind]
  rw [simple_eat_semi hh]
  change (simple M _).bind _ = _
  dsimp only
  rw [hsx]
  change (optExprBefore M .semi (locatedInput (cs ++ [.punct .semi])
    (locatedInput (vs ++ [.punct .rparen]) (locatedInput ts s)))).bind _ = _
  rw [hcv]
  change (optExprBefore M .rparen (locatedInput (vs ++ [.punct .rparen])
    (locatedInput ts s))).bind _ = _
  rw [hvv]
  change (stmt M ⟨true, u⟩ (locatedInput ts s)).bind _ = _
  rw [hb]
  rfl

mutual
/-- Coverage at every excess fuel and every framed suffix. -/
theorem atom_stmt_coverage : {k : SCtx} → {x : Syn (.stmt k)} → {ts : List Tok} → {d : Nat} →
    AtomStmt x ts d → ∀ (n : Nat) (s : St), StatementFrame x s → CatchFrame x s →
      stmt (n + d + 6) k (locatedInput ts s) = .ok (x, s)
  | k, _, _, b, .block (xs := xs) (parts := parts) h, n, s, _, _ => by
    have items := atom_items_at h (n + b + 4) (by omega)
    have hb := block_of_itemsAt xs parts.flatten (n + b + 4) (atom_items_count_le h) items s
    rw [blockInput_eq] at hb
    change stmt ((n + b + 5) + 1) k (blockInput parts.flatten s) = _
    rw [blockInput_eq, stmt_block_prefix, hb]
    rfl
  | k, _, _, _, .returnNone, n, s, _, _ => atom_empty_return n k s
  | _, _, _, _, .returnSome he hs, n, s, _, _ => atom_return_some he hs n s
  | _, _, _, _, .breakStmt, n, s, _, _ => break_coverage (n + 5) _ 0 0 0 0 s
  | _, _, _, _, .continueStmt, n, s, _, _ => continue_coverage (n + 5) _ 0 0 0 0 s
  | k, _, _, _, .ifNone (c := c) (x := x) (ts := ts) (d := d) (a := a) hc h, n, s, hf, hk => by
    have he : NoFollowingElse s := by
      rcases hf with hc' | he
      · cases hc'
      · exact he
    have hb := atom_stmt_coverage h (n + a) s (Or.inr he) hk
    rw [locatedInput_append]
    have fuel : n + (d + a + 1) + 6 = (n + d + 6) + a + 1 := by omega
    rw [fuel, if_atom_prefix hc]
    have fb : n + d + 6 + a = n + a + d + 6 := by omega
    change (stmt (n + d + 6 + a) k (locatedInput ts s)).bind (fun p =>
      ((do if ← eat (.kw .else_) then
             return Syn.ifStmt c p.1 (.some (← stmt (n + d + 6 + a) k))
           else return Syn.ifStmt c p.1 .none) : P (Syn (.stmt k))) p.2) = _
    rw [fb, hb]
    change (eat (.kw .else_) s).bind (fun p =>
      ((if p.1 then do
          return Syn.ifStmt c x (.some (← stmt (n + a + d + 6) k))
        else pure (Syn.ifStmt c x .none)) : P (Syn (.stmt k))) p.2) = _
    rw [eat_else_false s he]
    rfl
  | k, _, _, _, .ifSome (c := c) (t := t) (e := e) (ts := ts) (es := es) (d := d) (f := f)
      (a := a) hc ht he hcl, n, s, hf, hk => by
    let tail := locatedInput [.kw .else_] (locatedInput es s)
    have pt := atom_stmt_coverage ht (n + f + a) tail (Or.inl hcl)
      (Or.inr (by intro bad; cases bad))
    have pe := atom_stmt_coverage he (n + d + a) s hf hk
    have ft : n + f + a + d + 6 = n + (d + f) + 6 + a := by omega
    have fe : n + d + a + f + 6 = n + (d + f) + 6 + a := by omega
    rw [ft] at pt
    rw [fe] at pe
    rw [locatedInput_append, locatedInput_append, locatedInput_append]
    have fuel : n + (d + f + a + 1) + 6 = (n + (d + f) + 6) + a + 1 := by omega
    rw [fuel, if_atom_prefix hc]
    change (stmt (n + (d + f) + 6 + a) k (locatedInput ts tail)).bind (fun p =>
      ((do if ← eat (.kw .else_) then
             return Syn.ifStmt c p.1 (.some (← stmt (n + (d + f) + 6 + a) k))
           else return Syn.ifStmt c p.1 .none) : P (Syn (.stmt k))) p.2) = _
    rw [pt]
    change (stmt (n + (d + f) + 6 + a) k (locatedInput es s)).bind
      (fun p => .ok (Syn.ifStmt c t (.some p.1), p.2)) = _
    rw [pe]
    rfl
  | _, _, _, _, .whileLoop (l := l) (u := u) (d := d) (a := a) hc h, n, s, hf, hk => by
    rw [locatedInput_append]
    have fuel : n + (d + a + 1) + 6 = (n + d + 6) + a + 1 := by omega
    rw [fuel, while_atom_prefix hc]
    have fb : n + d + 6 + a = n + a + d + 6 := by omega
    rw [fb, atom_stmt_coverage h (n + a) s hf hk]
    rfl
  | _, _, _, _, .forLoop (l := l) (u := u) (ts := ts) (d := d) h, n, s, hf, hk => by
    rw [locatedInput_append, stmt]
    change (stmt (n + (d + 1) + 5) ⟨true, u⟩ (locatedInput ts s)).bind
      (fun p => .ok (Syn.forStmt (l := l) .none .none .none p.1, p.2)) = _
    have fuel : n + (d + 1) + 5 = n + d + 6 := by omega
    rw [fuel, atom_stmt_coverage h n s hf hk]
    rfl
  | _, _, _, _, .forAtom (l := l) (u := u) (x := x) (ts := ts) (d := d)
      (ca := ca) (va := va) hc hv h, n, s, hf, hk => by
    have hb := atom_stmt_coverage h (n + ca + va) s hf hk
    have fuel : n + (d + ca + va + 1) + 6 = (n + d + 1) + ca + va + 5 + 1 := by omega
    rw [show n + ca + va + d + 6 = (n + d + 1) + ca + va + 5 by omega] at hb
    rw [fuel]
    exact for_atom_step hc hv (n + d + 1) l s hb
  | _, _, _, _, .simpleS hx hh, n, s, _, _ => simple_stmt_coverage hx hh n s
  | _, _, _, _, .revertExpr hx hr, n, s, _, _ => revert_expr_coverage hx hr n s
  | _, _, _, _, .asm (a := a) hf hy hl, n, s, _, _ => by
    rw [show n + (a + 1) + 6 = (n + 6) + a + 1 by omega]
    exact asm_step hf hy hl (n + 6) s
  | k, _, _, _, .tryS (e := e) (es := es) (a := a) (xs := xs) (parts := parts) (b := b)
      (c := c) (cts := cts) (f := f) (cs := cs) (cparts := cparts) (g := g)
      he hi hbp hc hcs, n, s, _, hf => by
    have hk : NoFollowingCatch s := hf.resolve_left (by intro bad; cases bad)
    let S := locatedInput (cts ++ cparts.flatten) s
    have pe := he (n + b + f + g + 7) parts.flatten S hbp
    rw [show n + b + f + g + 7 + a = n + a + b + f + g + 7 by omega] at pe
    have pr := empty_rets_atom (n + a + b + f + g + 6) parts.flatten S
    have pb := block_of_itemsAt xs parts.flatten (n + a + b + f + g + 6)
      (atom_items_count_le hi) (atom_items_at hi (n + a + b + f + g + 6) (by omega)) S
    have pc : many (catchStep (n + a + b + f + g + 7) k) S = .ok (c :: g0ListValues cs, s) := by
      apply catches_many
      · have hl := atom_catches_count_le hcs
        have hh := atom_catch_head hc
        cases cts with
        | nil => cases hh
        | cons t tail =>
          simp only [List.cons_append, List.length_cons, List.length_append]
          omega
      · intro extra
        rw [locatedInput_append]
        exact many_aux_cons (atom_catch_step hc _ (by omega) _)
          (atom_catches_many_aux hcs _ (by omega) extra s hk)
    have step := try_step (k := k) (n + a + b + f + g + 7) es [] (braces parts.flatten) S S s
      (by simpa only [List.append_nil, List.nil_append, blockInput] using pe)
      (by simpa only [List.nil_append, blockInput] using pr)
      (by simpa only [blockInput] using pb) pc
    have hin : locatedInput ([.kw .try_] ++ es ++ braces parts.flatten ++ cts ++ cparts.flatten) s =
        locatedInput ([.kw .try_] ++ es ++ [] ++ braces parts.flatten) S := by
      simp only [S, ← locatedInput_append, List.append_assoc, List.nil_append]
    rw [hin, show n + (a + b + f + g + 2) + 6 = n + a + b + f + g + 7 + 1 by omega, step]
    change Except.ok (Syn.tryStmt e .nil (.block xs) c (toSynList (itemsAsList cs)), s) = _
    rw [itemsAsList_inverse]
  | k, _, _, _, .tryRets (e := e) (es := es) (a := a) (rets := rets) (rs := rs) (r := r)
      (xs := xs) (parts := parts) (b := b)
      (c := c) (cts := cts) (f := f) (cs := cs) (cparts := cparts) (g := g)
      he hr hi hc hcs, n, s, _, hf => by
    have hk : NoFollowingCatch s := hf.resolve_left (by intro bad; cases bad)
    let S := locatedInput (cts ++ cparts.flatten) s
    have pe := he (n + r + b + f + g + 7) (rs ++ braces parts.flatten) S
    rw [show n + r + b + f + g + 7 + a = n + a + r + b + f + g + 7 by omega] at pe
    have pr := hr (n + a + b + f + g + 7) parts.flatten S
    rw [show n + a + b + f + g + 7 + r = n + a + r + b + f + g + 7 by omega] at pr
    have pb := block_of_itemsAt xs parts.flatten (n + a + r + b + f + g + 6)
      (atom_items_count_le hi) (atom_items_at hi (n + a + r + b + f + g + 6) (by omega)) S
    have pc : many (catchStep (n + a + r + b + f + g + 7) k) S =
        .ok (c :: g0ListValues cs, s) := by
      apply catches_many
      · have hl := atom_catches_count_le hcs
        have hh := atom_catch_head hc
        cases cts with
        | nil => cases hh
        | cons t tail =>
          simp only [List.cons_append, List.length_cons, List.length_append]
          omega
      · intro extra
        rw [locatedInput_append]
        exact many_aux_cons (atom_catch_step hc _ (by omega) _)
          (atom_catches_many_aux hcs _ (by omega) extra s hk)
    have step := try_step (k := k) (n + a + r + b + f + g + 7) es (.kw .returns :: rs)
      (braces parts.flatten) S S s
      (by simpa only [List.append_assoc, List.cons_append] using pe)
      (by simpa only [blockInput] using pr)
      (by simpa only [blockInput] using pb) pc
    have hin : locatedInput ([.kw .try_] ++ es ++ (.kw .returns :: rs) ++ braces parts.flatten ++
        cts ++ cparts.flatten) s =
        locatedInput ([.kw .try_] ++ es ++ (.kw .returns :: rs) ++ braces parts.flatten) S := by
      simp only [S, ← locatedInput_append, List.append_assoc]
    rw [hin, show n + (a + r + b + f + g + 2) + 6 = n + a + r + b + f + g + 7 + 1 by omega, step]
    change Except.ok (Syn.tryStmt e rets (.block xs) c (toSynList (itemsAsList cs)), s) = _
    rw [itemsAsList_inverse]
  | _, _, _, b, .emitS hp ha hl _, n, s, _, _ => by
    rw [show n + b + 6 = (n + 5) + b + 1 by omega]
    exact emit_step hp ha hl (n + 5) s
  | _, _, _, b, .revertS hp ha hl _, n, s, _, _ => by
    rw [show n + b + 6 = (n + 5) + b + 1 by omega]
    exact revert_step hp ha hl (n + 5) s
  | _, _, _, _, .forInit (l := l) (u := u) (ts := ts) (d := d) (a := a) (ca := ca) (va := va)
      hx hh hc hv h, n, s, hf, hk => by
    have hb := atom_stmt_coverage h (n + a + ca + va) s hf hk
    rw [show n + a + ca + va + d + 6 = (n + d + 1) + a + ca + va + 5 by omega] at hb
    rw [show n + (d + a + ca + va + 1) + 6 = (n + d + 1) + a + ca + va + 5 + 1 by omega]
    exact for_init_step hx hh hc hv (n + d + 1) l s hb
  | _, _, _, _, .doLoop (l := l) (u := u) (c := c) (cs := cs) (x := x) (ts := ts) (d := d)
      (a := a) hc h, n, s, _, _ => by
    let tail := locatedInput ([.kw .while_, .punct .lparen] ++ cs ++
      [.punct .rparen, .punct .semi]) s
    have frame : StatementFrame x tail := Or.inr (by intro bad; cases bad)
    have hb := atom_stmt_coverage h (n + a) tail frame
      (Or.inr (by intro bad; cases bad))
    have fb : n + a + d + 6 = n + (d + a + 1) + 5 := by omega
    rw [fb] at hb
    have ht : locatedInput ([.kw .do_] ++ ts ++ [.kw .while_, .punct .lparen] ++ cs ++
        [.punct .rparen, .punct .semi]) s = locatedInput [.kw .do_] (locatedInput ts tail) := by
      simp only [tail, ← locatedInput_append, List.append_assoc]
    rw [ht, stmt]
    change (stmt (n + (d + a + 1) + 5) ⟨true, u⟩ (locatedInput ts tail)).bind (fun p =>
        ((do expect (.kw .while_) "'while'"
             expectP .lparen
             let c' ← expr (n + (d + a + 1) + 5)
             expectP .rparen
             expectP .semi
             pure (Syn.doWhile (l := l) p.1 c')) : P (Syn (.stmt ⟨l, u⟩))) p.2) = _
    rw [hb]
    have fa : n + (d + a + 1) + 5 = (n + d + 6) + a := by omega
    rw [fa]
    exact do_atom_tail hc (n + d + 6) l u x s

/-- The block parser's item loop at every fuel above the list budget. -/
theorem atom_items_at : {k : SCtx} → {xs : Syn (.list (.item k))} →
    {parts : List (List Tok)} → {b : Nat} → AtomItems xs parts b →
    ∀ fuel, b ≤ fuel → ItemsAt xs parts.flatten fuel
  | k, _, _, _, .nil, fuel, _ => by
    intro extra s
    simp only [itemCount_nil, itemsAsList_nil, List.flatten_nil]
    change manyAux _ (extra + 1) (endState s) = _
    exact many_aux_none (leaf_step_stop fuel k s)
  | k, _, _, _, .stmtCons (x := x) (xs := xs) (ts := ts) (parts := parts) (d := d) (b := b)
      hh ht, fuel, hf => by
    intro extra s
    simp only [itemCount_cons, itemsAsList_cons, List.flatten_cons]
    change manyAux _ ((extra + itemCount xs + 1) + 1)
      (locatedInput (ts ++ parts.flatten) (endState s)) = _
    rw [locatedInput_append]
    have enough : d + 7 ≤ fuel := by omega
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' enough
    have eqfuel : fuel = (n + d + 6) + 1 := by omega
    have frame : StatementFrame x (leafInput parts.flatten s) :=
      Or.inr (atom_items_no_else ht (endState s) (by intro bad; cases bad))
    have head : blockLeafStep fuel k (locatedInput ts (leafInput parts.flatten s)) =
        .ok (some (.stmtItem x), leafInput parts.flatten s) := by
      rw [eqfuel]
      have hk : NoFollowingCatch (leafInput parts.flatten s) :=
        atom_items_no_catch ht (endState s) (by intro bad; cases bad)
      exact atom_item_step hh (n + d + 6) _ (atom_stmt_coverage hh n _ frame (Or.inr hk))
    exact many_aux_cons head (atom_items_at ht fuel (by omega) extra s)
  | _, _, _, _, .uncheckedCons (l := l) (ys := ys) (xs := xs) (qs := qs) (parts := parts)
      (c := c) (b := b) hy ht, fuel, hf => by
    intro extra s
    simp only [itemCount_cons, itemsAsList_cons, List.flatten_cons]
    change manyAux _ ((extra + itemCount xs + 1) + 1)
      (locatedInput ((.kw .unchecked :: braces qs.flatten) ++ parts.flatten) (endState s)) = _
    rw [locatedInput_append]
    have enough : c + 2 ≤ fuel := by omega
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' enough
    have eqfuel : fuel = ((n + c) + 1) + 1 := by omega
    have inner := block_of_itemsAt ys qs.flatten (n + c) (atom_items_count_le hy)
      (atom_items_at hy (n + c) (by omega)) (leafInput parts.flatten s)
    have head : blockLeafStep fuel ⟨l, false⟩
        (uncheckedInput qs.flatten (leafInput parts.flatten s)) =
        .ok (some (.uncheckedItem (.block ys)), leafInput parts.flatten s) := by
      rw [eqfuel]
      exact step_unchecked_of_coverage ((n + c) + 1) l (.block ys) qs.flatten _ inner
    exact many_aux_cons head (atom_items_at ht fuel (by omega) extra s)

/-- One catch-loop step at every fuel above the clause budget. -/
theorem atom_catch_step : {k : SCtx} → {c : Syn (.catchClause k)} → {ts : List Tok} → {d : Nat} →
    AtomCatch c ts d → ∀ fuel, d ≤ fuel → ∀ s,
      catchStep fuel k (locatedInput ts s) = .ok (some c, s)
  | k, _, _, _, .plain (xs := xs) (parts := parts) (b := b) h, fuel, hf, s => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = (n + b + 1) + 1 := ⟨fuel - b - 2, by omega⟩
    have pb := block_of_itemsAt xs parts.flatten (n + b) (atom_items_count_le h)
      (atom_items_at h (n + b) (by omega)) s
    rw [catch_step_start _ k _ s rfl]
    have hi : locatedInput ([.kw .catch_] ++ braces parts.flatten) s =
        plainCatchInput parts.flatten s := by
      simp only [plainCatchInput, blockInput, tk, ← locatedInput_append]
    rw [hi, catch_plain_prefix, pb]
    rfl
  | k, _, _, _, .sig (name := name) (a := a) (xs := xs) (parts := parts) (b := b) hp hl h,
      fuel, hf, s => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = (n + b + 1) + a + 1 := ⟨fuel - a - b - 2, by omega⟩
    have pb := block_of_itemsAt xs parts.flatten (n + a + b) (atom_items_count_le h)
      (atom_items_at h (n + a + b) (by omega)) s
    rw [show n + a + b + 1 = n + b + 1 + a by omega] at pb
    rw [catch_step_start _ k _ s rfl, catch_sig_step name hp hl (n + b + 1) parts.flatten s s pb]
    rfl

/-- The catch loop over a clause list, ending at a suffix without `catch`. -/
theorem atom_catches_many_aux : {k : SCtx} → {cs : Syn (.list (.catchClause k))} →
    {parts : List (List Tok)} → {b : Nat} → AtomCatches cs parts b →
    ∀ fuel, b ≤ fuel → ∀ extra s, NoFollowingCatch s →
      manyAux (catchStep fuel k) (extra + g0ListLength cs + 1) (locatedInput parts.flatten s) =
        .ok (g0ListValues cs, s)
  | k, _, _, _, .nil, fuel, _, extra, s, hs => by
    simp only [g0ListLength_nil, g0ListValues_nil, List.flatten_nil, Nat.add_zero]
    change manyAux _ (extra + 1) s = _
    exact many_aux_none (catch_step_stop fuel k s hs)
  | k, _, _, _, .cons (cs := cs) (parts := parts) hc ht, fuel, hf, extra, s, hs => by
    simp only [g0ListLength_cons, g0ListValues_cons, List.flatten_cons]
    rw [locatedInput_append]
    change manyAux _ ((extra + g0ListLength cs + 1) + 1) _ = _
    exact many_aux_cons (atom_catch_step hc fuel (by omega) _)
      (atom_catches_many_aux ht fuel (by omega) extra s hs)
end

/-- Block-statement, block and unchecked-item coverage for item lists. -/
theorem atom_items_block_coverage {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} {b : Nat} (h : AtomItems xs parts b) (n : Nat) (s : St) :
    block (n + b + 1) k (blockInput parts.flatten s) = .ok (.block xs, s) :=
  block_of_itemsAt xs parts.flatten (n + b) (atom_items_count_le h)
    (atom_items_at h (n + b) (by omega)) s

theorem atom_items_unchecked_coverage {l : Bool} {xs : Syn (.list (.item ⟨l, true⟩))}
    {parts : List (List Tok)} {b : Nat} (h : AtomItems xs parts b) (n : Nat) (s : St) :
    item (n + b + 2) ⟨l, false⟩ (uncheckedInput parts.flatten s) =
      .ok (.uncheckedItem (.block xs), s) := by
  rw [uncheckedInput_eq, item_unchecked_prefix, atom_items_block_coverage h]
  rfl

/-- A statement with no `try` node anywhere is not catch-open. -/
theorem catchOpen_false_of_no_try : {k : SCtx} → (x : Syn (.stmt k)) →
    Ctor.tryStmt ∉ x.nodes.map Node.ctor → catchOpen x = false
  | _, .ifStmt c t .none, h => catchOpen_false_of_no_try t (fun ht => h (by
      simp only [Syn.nodes, Syn.node, Syn.ctor, List.map_cons, List.map_append, List.mem_cons,
        List.mem_append, ht, true_or, or_true]))
  | _, .ifStmt c t (.some e), h => catchOpen_false_of_no_try e (fun he => h (by
      simp only [Syn.nodes, Syn.node, Syn.ctor, List.map_cons, List.map_append, List.mem_cons,
        List.mem_append, he, or_true]))
  | _, .forStmt i c u b, h => catchOpen_false_of_no_try b (fun hb => h (by
      simp only [Syn.nodes, Syn.node, Syn.ctor, List.map_cons, List.map_append, List.mem_cons,
        List.mem_append, hb, or_true]))
  | _, .whileStmt c b, h => catchOpen_false_of_no_try b (fun hb => h (by
      simp only [Syn.nodes, Syn.node, Syn.ctor, List.map_cons, List.map_append, List.mem_cons,
        List.mem_append, hb, or_true]))
  | _, .tryStmt .., h => absurd (by
      simp only [Syn.nodes, Syn.node, Syn.ctor, List.map_cons, List.mem_cons, true_or]) h
  | _, .blockStmt _, _ => rfl
  | _, .simpleStmt _, _ => rfl
  | _, .doWhile _ _, _ => rfl
  | _, .continueStmt, _ => rfl
  | _, .breakStmt, _ => rfl
  | _, .returnStmt _, _ => rfl
  | _, .emit _ _, _ => rfl
  | _, .revert _ _, _ => rfl
  | _, .assembly _ _ _, _ => rfl

/-- The catch frame of every `try`-free statement, at every suffix. -/
theorem catch_frame_of_no_try {k : SCtx} (x : Syn (.stmt k)) (s : St)
    (h : Ctor.tryStmt ∉ g0NodeCtors x) : CatchFrame x s :=
  Or.inl (catchOpen_false_of_no_try x (by rw [← g0NodeCtors_eq_nodes]; exact h))

/-- Coverage of a `try`-free statement needs only the else frame. -/
theorem atom_stmt_coverage_no_try {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok} {d : Nat}
    (hx : AtomStmt x ts d) (h : Ctor.tryStmt ∉ g0NodeCtors x) (n : Nat) (s : St)
    (hf : StatementFrame x s) : stmt (n + d + 6) k (locatedInput ts s) = .ok (x, s) :=
  atom_stmt_coverage hx n s hf (catch_frame_of_no_try x s h)

/-- The root keeps the immutable precedence node contract. -/
theorem atom_stmt_node {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok} {d : Nat}
    (h : AtomStmt x ts d) : x.precNode = true := by
  cases h with
  | ifSome _ _ _ hc => exact (if_some_contract_iff _ _ _).mpr hc
  | emitS _ _ _ hpath => exact hpath
  | revertS _ _ _ hpath => exact hpath
  | _ => rfl

theorem atom_stmt_nearest_else {k : SCtx} {c : Syn .expr} {t e : Syn (.stmt k)}
    {ts : List Tok} {d : Nat} (h : AtomStmt (.ifStmt c t (.some e)) ts d) : ¬ OpenSpine t :=
  nearestElse_node _ _ _ (atom_stmt_node h)

/-- Two witnesses over the same tokens are the same tree (the parser is a
function); atoms enter only through their exposed parse premises. -/
theorem atom_stmt_token_unique {k : SCtx} {x y : Syn (.stmt k)}
    {ts us : List Tok} {d e : Nat} (hx : AtomStmt x ts d)
    (hy : AtomStmt y us e) (he : ts = us) : x = y := by
  subst us
  let s : St := ⟨[], [], 0⟩
  have frame (z : Syn (.stmt k)) : StatementFrame z s := Or.inr (by intro bad; cases bad)
  have px := atom_stmt_coverage hx e s (frame x) (Or.inr (by intro bad; cases bad))
  have py := atom_stmt_coverage hy d s (frame y) (Or.inr (by intro bad; cases bad))
  have hf : e + d + 6 = d + e + 6 := by omega
  rw [hf] at px
  exact congrArg Prod.fst (Except.ok.inj (px.symm.trans py))

/-- A statement prefix and its suffix are determined by the token string. -/
theorem atom_stmt_prefix_unique {k : SCtx} {x y : Syn (.stmt k)}
    {ts us rest tail : List Tok} {d e : Nat} (hx : AtomStmt x ts d)
    (hy : AtomStmt y us e) (s : St)
    (fx : StatementFrame x (locatedInput rest s))
    (fy : StatementFrame y (locatedInput tail s))
    (cx : CatchFrame x (locatedInput rest s)) (cy : CatchFrame y (locatedInput tail s))
    (he : ts ++ rest = us ++ tail) : x = y ∧ rest = tail := by
  have input : locatedInput ts (locatedInput rest s) = locatedInput us (locatedInput tail s) := by
    rw [← locatedInput_append, ← locatedInput_append, he]
  have px := atom_stmt_coverage hx e (locatedInput rest s) fx cx
  have py := atom_stmt_coverage hy d (locatedInput tail s) fy cy
  have fuel : e + d + 6 = d + e + 6 := by omega
  rw [fuel, input] at px
  have pair := Except.ok.inj (px.symm.trans py)
  have suffix := congrArg (fun p => p.2.ts.map (fun t : Located => t.tok)) pair
  simp only [locatedInput, List.map_append, List.map_map, Function.comp_def, atToken,
    List.map_id'] at suffix
  exact ⟨congrArg Prod.fst pair, List.append_cancel_right suffix⟩

/-- Every control-leaf item list is a nested item list with budget at most seven. -/
theorem atom_items_of_leaf_items {k : SCtx} {xs : Syn (.list (.item k))} {ts : List Tok}
    (h : LeafItems xs ts) : ∃ parts b, parts.flatten = ts ∧ b ≤ 7 ∧ AtomItems xs parts b := by
  induction h with
  | nil => exact ⟨[], 0, rfl, by omega, .nil⟩
  | @returnCons k xs ts h ih =>
    obtain ⟨parts, b, hp, hb, hi⟩ := ih
    refine ⟨[.kw .return_, .punct .semi] :: parts, max (0 + 7) b, ?_, by omega,
      .stmtCons .returnNone hi⟩
    simp only [List.flatten_cons, hp, List.cons_append, List.nil_append]
  | @breakCons u xs ts h ih =>
    obtain ⟨parts, b, hp, hb, hi⟩ := ih
    refine ⟨[.kw .break_, .punct .semi] :: parts, max (0 + 7) b, ?_, by omega,
      .stmtCons .breakStmt hi⟩
    simp only [List.flatten_cons, hp, List.cons_append, List.nil_append]
  | @continueCons u xs ts h ih =>
    obtain ⟨parts, b, hp, hb, hi⟩ := ih
    refine ⟨[.kw .continue_, .punct .semi] :: parts, max (0 + 7) b, ?_, by omega,
      .stmtCons .continueStmt hi⟩
    simp only [List.flatten_cons, hp, List.cons_append, List.nil_append]

#print axioms bool_atom_semi
#print axioms ident_atom_semi
#print axioms atom_stmt_no_else_input
#print axioms atom_stmt_tokens_nonempty
#print axioms atom_items_no_else
#print axioms atom_items_count_le
#print axioms atom_item_step
#print axioms atom_empty_return
#print axioms atom_return_some
#print axioms isP_false_of_head
#print axioms opt_atom_coverage
#print axioms for_empty_init_prefix
#print axioms for_atom_step
#print axioms for_init_step
#print axioms atom_stmt_coverage
#print axioms atom_items_at
#print axioms atom_catch_step
#print axioms atom_catches_many_aux
#print axioms atom_catch_head
#print axioms atom_catches_count_le
#print axioms atom_stmt_no_catch_input
#print axioms atom_items_no_catch
#print axioms atom_items_block_coverage
#print axioms atom_items_unchecked_coverage
#print axioms catchOpen_false_of_no_try
#print axioms catch_frame_of_no_try
#print axioms atom_stmt_coverage_no_try
#print axioms atom_stmt_node
#print axioms atom_stmt_nearest_else
#print axioms atom_stmt_token_unique
#print axioms atom_stmt_prefix_unique
#print axioms atom_items_of_leaf_items
end Solidity.Frontend.StatementGrammarH28
