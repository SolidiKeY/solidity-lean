import Solidity.Frontend.StatementGrammarH28.AtomCall
import Solidity.Frontend.StatementGrammarH28.CatchListCoverage
import Solidity.Frontend.StatementGrammarH28.BlockHeaderBoundary

/-! `try` statements and catch clauses over stated sub-parser premises.

The tried expression enters through `ExprAtomBrace` (the existing `expr`
parser reads exactly `es` as `e` and stops at the success block's `{`,
whenever that block's body does not start with `ident :`, the call-options
lookahead of `postLoop`) or, with a `returns` clause, through
`ExprAtomReturns` (stops at `returns`). The return parameters enter through
`RetsAtom` on the existing `returnsOpt` parser and catch parameters through
`ParamsAtom` on the existing `paramsParen` parser, each stopping at the
following block's `{`. All four are proved here only for small instances
(identifiers; no return parameters and `returns (bool)`; `(bool)` and
`(bool x)`); otherwise they are premises. No expression, type or parameter
completeness and no expression uniqueness (SOL-EU) is claimed. The composition
lemmas below are the actual parser equations; the recursive coverage is in
`AtomNested`. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- The catch-open spine: a `try` statement, or a conditional or loop whose
last sub-statement is catch-open. Its catch loop is greedy, so only such a
statement needs a following-catch frame (the analogue of `Syn.openIf`). -/
def catchOpen : {c : Cat} → Syn c → Bool
  | _, .ifStmt _ t .none => catchOpen t
  | _, .ifStmt _ _ (.some e) => catchOpen e
  | _, .forStmt _ _ _ b => catchOpen b
  | _, .whileStmt _ b => catchOpen b
  | _, .tryStmt .. => true
  | _, _ => false

/-- A catch-open statement must not be followed by a `catch`. -/
def CatchFrame {k : SCtx} (x : Syn (.stmt k)) (s : St) : Prop :=
  catchOpen x = false ∨ NoFollowingCatch s

/-- Expression premise before a success block whose body does not start with
the named-argument pair `ident :`, with fuel budget `a`. -/
def ExprAtomBrace (e : Syn .expr) (es : List Tok) (a : Nat) : Prop :=
  ∀ (n : Nat) (body : List Tok) (s : St), NoNamedFrame (body ++ pu .rbrace) →
    expr (n + a) (locatedInput (es ++ braces body) s) = .ok (e, blockInput body s)

/-- Expression premise before a `returns` clause, with fuel budget `a`. -/
def ExprAtomReturns (e : Syn .expr) (es : List Tok) (a : Nat) : Prop :=
  ∀ (n : Nat) (rest : List Tok) (s : St),
    expr (n + a) (locatedInput (es ++ .kw .returns :: rest) s) =
      .ok (e, locatedInput (.kw .returns :: rest) s)

/-- Return-parameter premise on `returnsOpt` before a block, with budget `r`. -/
def RetsAtom (rets : Syn (.list .param)) (rs : List Tok) (r : Nat) : Prop :=
  ∀ (n : Nat) (body : List Tok) (s : St),
    returnsOpt (n + r) (locatedInput (rs ++ braces body) s) = .ok (rets, blockInput body s)

/-- Catch-parameter premise on `paramsParen` before a block, with budget `a`. -/
def ParamsAtom (ps : Syn (.list .param)) (pts : List Tok) (a : Nat) : Prop :=
  ∀ (n : Nat) (body : List Tok) (s : St),
    paramsParen (n + a) (locatedInput (pts ++ braces body) s) = .ok (ps, blockInput body s)

theorem ident_expr_brace (x : String) : ExprAtomBrace (.ident x) [.ident x] 5 := by
  intro n body s hb
  have hpost := postLoop_no_named_lookahead n (.ident x) (blockInput body s) rfl (by
    simpa only [blockInput, locatedInput, braces, pu, List.map_append, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero,
      List.map_map, Function.comp_def, atToken, List.map_id', List.append_assoc]
      using hb (s.ts.map (fun t : Located => t.tok)))
  rw [expr, binary, unary]
  change ((postLoop (n + 1) (.ident x) (blockInput body s)).bind
    (fun p => binLoop (n + 3) 2 p.1 p.2)).bind (fun p =>
    ((do
      let lhs := p.1
      match ← peek with
      | some t =>
        match assignOf t with
        | some op => do advance; return Syn.assign op lhs (← expr (n + 4))
        | none =>
          if t == .punct .question then
            advance
            let a ← expr (n + 4)
            expectP .colon
            let b ← expr (n + 4)
            return Syn.cond lhs a b
          else return lhs
      | none => return lhs) : P (Syn .expr)) p.2) = _
  rw [hpost]
  rfl

theorem ident_expr_returns (x : String) : ExprAtomReturns (.ident x) [.ident x] 5 :=
  fun _ _ _ => rfl

theorem empty_rets_atom : RetsAtom .nil [] 1 :=
  fun _ _ _ => rfl

theorem bool_params_atom (x : Option String) :
    ParamsAtom (.cons (.param (.elem .bool) .none x) .nil)
      (parens ([.elem .bool] ++ optToks idt x)) 5 := by
  intro n body s
  cases x <;> rfl

theorem bool_rets_atom :
    RetsAtom (.cons (.param (.elem .bool) .none .none) .nil)
      [.kw .returns, .punct .lparen, .elem .bool, .punct .rparen] 6 :=
  fun _ _ _ => rfl

/-- The actual `try` branch of `stmt`, given its four sub-parser results. -/
theorem try_step {k : SCtx} {e : Syn .expr} {rets : Syn (.list .param)} {b : Syn (.block k)}
    {c : Syn (.catchClause k)} {rest : List (Syn (.catchClause k))}
    (N : Nat) (es rs bs : List Tok) (S S' out : St)
    (he : expr N (locatedInput (es ++ rs ++ bs) S) = .ok (e, locatedInput (rs ++ bs) S))
    (hr : returnsOpt N (locatedInput (rs ++ bs) S) = .ok (rets, locatedInput bs S))
    (hb : block N k (locatedInput bs S) = .ok (b, S'))
    (hc : many (catchStep N k) S' = .ok (c :: rest, out)) :
    stmt (N + 1) k (locatedInput ([.kw .try_] ++ es ++ rs ++ bs) S) =
      .ok (.tryStmt e rets b c (toSynList rest), out) := by
  have hi : locatedInput ([.kw .try_] ++ es ++ rs ++ bs) S =
      locatedInput [.kw .try_] (locatedInput (es ++ rs ++ bs) S) := by
    simp only [← locatedInput_append, List.append_assoc]
  rw [hi, stmt]
  change (expr N (locatedInput (es ++ rs ++ bs) S)).bind (fun p =>
    ((do let rets ← returnsOpt N
         let b ← block N k
         let cs ← many (catchStep N k)
         match cs with
         | c :: rest => return Syn.tryStmt p.1 rets b c (toSynList rest)
         | [] => P.fail "expected a catch clause") : P (Syn (.stmt k))) p.2) = _
  rw [he]
  change (returnsOpt N (locatedInput (rs ++ bs) S)).bind (fun p =>
    ((do let b ← block N k
         let cs ← many (catchStep N k)
         match cs with
         | c :: rest => return Syn.tryStmt e p.1 b c (toSynList rest)
         | [] => P.fail "expected a catch clause") : P (Syn (.stmt k))) p.2) = _
  rw [hr]
  change (block N k (locatedInput bs S)).bind (fun p =>
    ((do let cs ← many (catchStep N k)
         match cs with
         | c :: rest => return Syn.tryStmt e rets p.1 c (toSynList rest)
         | [] => P.fail "expected a catch clause") : P (Syn (.stmt k))) p.2) = _
  rw [hb]
  change (many (catchStep N k) S').bind (fun p =>
    ((match p.1 with
      | c :: rest => pure (Syn.tryStmt e rets b c (toSynList rest))
      | [] => P.fail "expected a catch clause") : P (Syn (.stmt k))) p.2) = _
  rw [hc]
  rfl

/-- The actual `many` over catch steps from its token-derived counter. -/
theorem catches_many {k : SCtx} {c : Syn (.catchClause k)} {cs : Syn (.list (.catchClause k))}
    (ts : List Tok) (fuel : Nat) (s : St) (hlen : g0ListLength cs + 1 ≤ ts.length)
    (haux : ∀ extra, manyAux (catchStep fuel k) (extra + g0ListLength cs + 1 + 1)
      (locatedInput ts s) = .ok (c :: g0ListValues cs, s)) :
    many (catchStep fuel k) (locatedInput ts s) = .ok (c :: g0ListValues cs, s) := by
  have length : (locatedInput ts s).ts.length = ts.length + s.ts.length := by
    simp only [locatedInput, List.length_append, List.length_map]
  let extra := (locatedInput ts s).ts.length - (g0ListLength cs + 1)
  have counter : (locatedInput ts s).ts.length + 1 = extra + g0ListLength cs + 1 + 1 := by
    omega
  change manyAux _ ((locatedInput ts s).ts.length + 1) _ = _
  rw [counter]
  exact haux extra

/-- The actual signature branch of `catchClause`, given the parameter premise
and the body block. -/
theorem catch_sig_step {k : SCtx} {p : Syn .param} {ps : Syn (.list .param)} {pts : List Tok}
    {a : Nat} {b : Syn (.block k)} (name : Option String)
    (hp : ParamsAtom (.cons p ps) pts a) (hl : pts.head? = some (.punct .lparen))
    (m : Nat) (body : List Tok) (s out : St)
    (hb : block (m + a) k (blockInput body s) = .ok (b, out)) :
    catchClause (m + a + 1) k
      (locatedInput ([.kw .catch_] ++ optToks idt name ++ pts ++ braces body) s) =
      .ok (.catchSig name p ps b, out) := by
  obtain ⟨tail, rfl⟩ : ∃ tail, pts = .punct .lparen :: tail := by
    cases pts with
    | nil => cases hl
    | cons t tail =>
      cases hl
      exact ⟨tail, rfl⟩
  have hparams := hp m body s
  cases name with
  | none =>
    rw [catchClause]
    change (paramsParen (m + a) (locatedInput (.punct .lparen :: tail ++ braces body) s)).bind
      (fun q => ((match q.1 with
        | .cons p rest => do return Syn.catchSig none p rest (← block (m + a) k)
        | .nil => P.fail "empty catch parameters") : P (Syn (.catchClause k))) q.2) = _
    rw [hparams]
    change (block (m + a) k (blockInput body s)).bind
      (fun q => .ok (Syn.catchSig none p ps q.1, q.2)) = _
    rw [hb]
    rfl
  | some y =>
    rw [catchClause]
    change (paramsParen (m + a) (locatedInput (.punct .lparen :: tail ++ braces body) s)).bind
      (fun q => ((match q.1 with
        | .cons p rest => do return Syn.catchSig (some y) p rest (← block (m + a) k)
        | .nil => P.fail "empty catch parameters") : P (Syn (.catchClause k))) q.2) = _
    rw [hparams]
    change (block (m + a) k (blockInput body s)).bind
      (fun q => .ok (Syn.catchSig (some y) p ps q.1, q.2)) = _
    rw [hb]
    rfl

#print axioms ident_expr_brace
#print axioms ident_expr_returns
#print axioms empty_rets_atom
#print axioms bool_rets_atom
#print axioms bool_params_atom
#print axioms try_step
#print axioms catches_many
#print axioms catch_sig_step
end Solidity.Frontend.StatementGrammarH28
