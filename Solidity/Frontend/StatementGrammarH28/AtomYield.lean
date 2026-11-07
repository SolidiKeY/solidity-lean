import Solidity.Frontend.StatementGrammarH28.AtomConditional

/-! Yield and `Derives` uniqueness for the atom-condition fragment.

The printer side of an atom is a stated premise, `AtomYield c cs`: the
existing printer yields exactly the tokens `cs` for `c`, independently of the
layout choices. It is proved here for identifiers and Boolean literals.
`AtomYields` mirrors `AtomStatements` with these printer premises; with both
witnesses, a tree's `Derives` set is exactly its token list, and two trees
deriving the same words are equal. No expression uniqueness (SOL-EU) is
assumed: atoms enter only through their stated parse and print premises. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- The printer premise for an expression atom. -/
def AtomYield (c : Syn .expr) (cs : List Tok) : Prop :=
  ∀ L : List Choice, c.yield L = some ([cs], L)

theorem ident_atom_yield (x : String) : AtomYield (.ident x) [.ident x] := fun _ => rfl

theorem bool_atom_yield (b : Bool) : AtomYield (.lit (.bool b)) [.bool b] := fun _ => rfl

/-- The printed tokens of the atom-condition fragment. -/
inductive AtomYields : {k : SCtx} → Syn (.stmt k) → List Tok → Prop where
  | boolean {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok} {d : Nat} :
      BooleanStatements x ts d → AtomYields x ts
  | ifNone {k : SCtx} {c : Syn .expr} {cs : List Tok} {x : Syn (.stmt k)} {ts : List Tok} :
      AtomYield c cs → AtomYields x ts →
      AtomYields (.ifStmt c x .none) ([.kw .if_, .punct .lparen] ++ cs ++ [.punct .rparen] ++ ts)
  | ifSome {k : SCtx} {c : Syn .expr} {cs : List Tok} {t e : Syn (.stmt k)} {ts es : List Tok} :
      AtomYield c cs → AtomYields t ts → AtomYields e es →
      AtomYields (.ifStmt c t (.some e))
        ([.kw .if_, .punct .lparen] ++ cs ++ [.punct .rparen] ++ ts ++ [.kw .else_] ++ es)
  | whileLoop {l u : Bool} {c : Syn .expr} {cs : List Tok} {x : Syn (.stmt ⟨true, u⟩)}
      {ts : List Tok} :
      AtomYield c cs → AtomYields x ts →
      AtomYields (Syn.whileStmt (l := l) c x)
        ([.kw .while_, .punct .lparen] ++ cs ++ [.punct .rparen] ++ ts)
  | forLoop {l u : Bool} {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} :
      AtomYields x ts → AtomYields (Syn.forStmt (l := l) .none .none .none x)
        ([.kw .for_, .punct .lparen, .punct .semi, .punct .semi, .punct .rparen] ++ ts)
  | doLoop {l u : Bool} {c : Syn .expr} {cs : List Tok} {x : Syn (.stmt ⟨true, u⟩)}
      {ts : List Tok} :
      AtomYield c cs → AtomYields x ts →
      AtomYields (Syn.doWhile (l := l) x c)
        ([.kw .do_] ++ ts ++ [.kw .while_, .punct .lparen] ++ cs ++ [.punct .rparen, .punct .semi])

theorem atom_yields_yield {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok}
    (h : AtomYields x ts) (L : List Choice) : x.yield L = some ([ts], L) := by
  induction h generalizing L with
  | boolean h => exact boolean_statements_yield h L
  | @ifNone k c cs x ts hc h ih =>
    rw [Syn.yield]
    change (c.yield L).bind (fun p => (x.yield p.2).bind (fun q =>
      ((Syn.none : Syn (.opt (.stmt k))).yield q.2).bind (fun r =>
        some ([tk .if_ ++ parens p.1.flatten ++ q.1.flatten ++
          (match r.1 with | [s] => tk .else_ ++ s | _ => [])], r.2)))) = _
    have hn : (Syn.none : Syn (.opt (.stmt k))).yield L = some ([], L) := rfl
    rw [hc L]
    simp only [Option.bind_some, ih, hn, List.flatten_cons, List.flatten_nil, List.append_nil,
      tk, parens, pu, List.cons_append, List.nil_append, List.append_assoc]
  | @ifSome k c cs t e ts es hc ht he iht ihe =>
    rw [Syn.yield]
    change (c.yield L).bind (fun p => (t.yield p.2).bind (fun q =>
      ((Syn.some e).yield q.2).bind (fun r =>
        some ([tk .if_ ++ parens p.1.flatten ++ q.1.flatten ++
          (match r.1 with | [s] => tk .else_ ++ s | _ => [])], r.2)))) = _
    have opt : (Syn.some e).yield L = some ([es], L) := by
      rw [Syn.yield]
      change (e.yield L).bind (fun p => some ([p.1.flatten], p.2)) = _
      rw [ihe]
      simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [hc L]
    simp only [Option.bind_some, iht, opt, List.flatten_cons, List.flatten_nil, List.append_nil,
      tk, parens, pu, List.cons_append, List.nil_append, List.append_assoc]
  | @whileLoop l u c cs x ts hc h ih =>
    rw [Syn.yield]
    change (c.yield L).bind (fun p => (x.yield p.2).bind (fun q =>
      some ([tk .while_ ++ parens p.1.flatten ++ q.1.flatten], q.2))) = _
    rw [hc L]
    simp only [Option.bind_some, ih, List.flatten_cons, List.flatten_nil, List.append_nil,
      tk, parens, pu, List.cons_append, List.nil_append, List.append_assoc]
  | forLoop h ih =>
    rw [Syn.yield]
    change (Syn.yield _ L).bind _ = _
    rw [ih]
    simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil,
      tk, parens, pu, List.cons_append, List.nil_append]
    rfl
  | @doLoop l u c cs x ts hc h ih =>
    rw [Syn.yield]
    change (x.yield L).bind (fun p => (c.yield p.2).bind (fun q =>
      some ([tk .do_ ++ p.1.flatten ++ tk .while_ ++ parens q.1.flatten ++ pu .semi], q.2))) = _
    rw [ih]
    simp only [Option.bind_some, hc L, List.flatten_cons, List.flatten_nil, List.append_nil,
      tk, parens, pu, List.cons_append, List.nil_append, List.append_assoc]

/-- A tree's derivations are exactly its printed tokens. -/
theorem atom_yields_derives_iff {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok}
    (h : AtomYields x ts) (words : List Tok) : x.Derives words ↔ words = ts := by
  constructor
  · intro ⟨L, hy⟩
    unfold Syn.toks at hy
    rw [atom_yields_yield h L] at hy
    cases L with
    | nil =>
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, Option.some.injEq] at hy
      exact hy.symm
    | cons choice rest => cases hy
  · intro he
    subst words
    refine ⟨[], ?_⟩
    unfold Syn.toks
    rw [atom_yields_yield h []]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

/-- Yield uniqueness inside the fragment: two trees with parse and print
witnesses deriving the same words are equal. -/
theorem atom_statements_yield_unique {k : SCtx} {x y : Syn (.stmt k)}
    {ts us words : List Tok} {d e : Nat}
    (hx : AtomStatements x ts d) (px : AtomYields x ts)
    (hy : AtomStatements y us e) (py : AtomYields y us)
    (dx : x.Derives words) (dy : y.Derives words) : x = y :=
  atom_statements_token_unique hx hy
    (((atom_yields_derives_iff px words).mp dx).symm.trans
      ((atom_yields_derives_iff py words).mp dy))

#print axioms ident_atom_yield
#print axioms bool_atom_yield
#print axioms atom_yields_yield
#print axioms atom_yields_derives_iff
#print axioms atom_statements_yield_unique

end Solidity.Frontend.StatementGrammarH28
