import Solidity.Frontend.StatementGrammarH28.ConditionalCoverage

/-! Actual yield and parser-based uniqueness for the recursive Boolean fragment.
Nearest else is enforced by the immutable precedence node contract. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem boolean_loops_closed {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok} {d : Nat}
    (h : BooleanLoops x ts d) : x.openIf = false := by
  induction h with
  | block => rfl
  | whileLoop h ih => exact ih
  | forLoop h ih => exact ih
  | doLoop => rfl

theorem boolean_statements_node {k : SCtx} {x : Syn (.stmt k)}
    {ts : List Tok} {d : Nat} (h : BooleanStatements x ts d) : x.precNode = true := by
  cases h with
  | loops h => cases h <;> rfl
  | ifNone => rfl
  | ifSome ht he hc => exact (if_some_contract_iff _ _ _).mpr hc
  | whileLoop => rfl
  | forLoop => rfl
  | doLoop => rfl

theorem boolean_statements_nearest_else {k : SCtx} {b : Bool} {t e : Syn (.stmt k)}
    {ts : List Tok} {d : Nat}
    (h : BooleanStatements (.ifStmt (.lit (.bool b)) t (.some e)) ts d) : ¬ OpenSpine t :=
  nearestElse_node _ _ _ (boolean_statements_node h)

theorem boolean_statements_yield {k : SCtx} {x : Syn (.stmt k)}
    {ts : List Tok} {d : Nat} (h : BooleanStatements x ts d) (L : List Choice) :
    x.yield L = some ([ts], L) := by
  induction h with
  | loops h => exact boolean_loops_yield h L
  | @ifNone k b x ts d h ih =>
    rw [Syn.yield]
    change (x.yield L).bind (fun p =>
      some ([tk .if_ ++ parens [.bool b] ++ p.1.flatten ++ []], p.2)) = _
    rw [ih]
    simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil,
      tk, parens, pu, List.cons_append, List.nil_append]
  | @ifSome k b t e ts es d f ht he hc iht ihe =>
    have opt : (Syn.some e).yield L = some ([es], L) := by
      rw [Syn.yield]
      change (e.yield L).bind (fun p => some ([p.1.flatten], p.2)) = _
      rw [ihe]
      simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [Syn.yield]
    change (t.yield L).bind (fun p => ((Syn.some e).yield p.2).bind (fun q =>
      some ([tk .if_ ++ parens [.bool b] ++ p.1.flatten ++
        (match q.1 with | [s] => tk .else_ ++ s | _ => [])], q.2))) = _
    rw [iht]
    change ((Syn.some e).yield L).bind (fun q =>
      some ([tk .if_ ++ parens [.bool b] ++ [ts].flatten ++
        (match q.1 with | [s] => tk .else_ ++ s | _ => [])], q.2)) = _
    rw [opt]
    simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil,
      tk, parens, pu, List.cons_append, List.nil_append, List.append_assoc]
  | @whileLoop l u b x ts d h ih =>
    rw [Syn.yield]
    change (x.yield L).bind (fun p =>
      some ([tk .while_ ++ parens [.bool b] ++ p.1.flatten], p.2)) = _
    rw [ih]
    simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil,
      tk, parens, pu, List.cons_append, List.nil_append]
  | forLoop h ih =>
    rw [Syn.yield]
    change (Syn.yield _ L).bind _ = _
    rw [ih]
    simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil,
      tk, parens, pu, List.cons_append, List.nil_append]
    rfl
  | @doLoop l u b x ts d h ih =>
    rw [Syn.yield]
    change (x.yield L).bind (fun p =>
      some ([tk .do_ ++ p.1.flatten ++ tk .while_ ++ parens [.bool b] ++ pu .semi], p.2)) = _
    rw [ih]
    simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil,
      tk, parens, pu, List.append_assoc, List.cons_append, List.nil_append]

theorem boolean_statements_token_unique {k : SCtx} {x y : Syn (.stmt k)}
    {ts us : List Tok} {d e : Nat} (hx : BooleanStatements x ts d)
    (hy : BooleanStatements y us e) (he : ts = us) : x = y := by
  subst us
  let s : St := ⟨[], [], 0⟩
  have frame (z : Syn (.stmt k)) : StatementFrame z s := Or.inr (by intro bad; cases bad)
  have px := boolean_statements_coverage hx e s (frame x)
  have py := boolean_statements_coverage hy d s (frame y)
  have hf : e + d + 6 = d + e + 6 := by omega
  rw [hf] at px
  exact congrArg Prod.fst (Except.ok.inj (px.symm.trans py))

theorem boolean_statements_derives_iff {k : SCtx} {x : Syn (.stmt k)}
    {ts : List Tok} {d : Nat} (h : BooleanStatements x ts d) (words : List Tok) :
    x.Derives words ↔ words = ts := by
  constructor
  · intro ⟨L, hy⟩
    unfold Syn.toks at hy
    rw [boolean_statements_yield h L] at hy
    cases L with
    | nil =>
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hy
      exact (Option.some.inj hy).symm
    | cons choice rest => cases hy
  · intro he
    subst words
    refine ⟨[], ?_⟩
    unfold Syn.toks
    rw [boolean_statements_yield h []]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

/-- No expression-uniqueness or assumed parser-success premise occurs here. -/
theorem boolean_statements_yield_unique {k : SCtx} {x y : Syn (.stmt k)}
    {ts us words : List Tok} {d e : Nat} (hx : BooleanStatements x ts d)
    (hy : BooleanStatements y us e) (dx : x.Derives words) (dy : y.Derives words) : x = y :=
  boolean_statements_token_unique hx hy
    (((boolean_statements_derives_iff hx words).mp dx).symm.trans
      ((boolean_statements_derives_iff hy words).mp dy))

/-- For framed actual prefixes, common structural fuel recovers both syntax
and the token suffix. Arbitrary suffix locations/layout/EOF remain unchanged. -/
theorem boolean_statements_prefix_unique {k : SCtx} {x y : Syn (.stmt k)}
    {ts us rest tail : List Tok} {d e : Nat} (hx : BooleanStatements x ts d)
    (hy : BooleanStatements y us e) (s : St)
    (fx : StatementFrame x (locatedInput rest s))
    (fy : StatementFrame y (locatedInput tail s))
    (he : ts ++ rest = us ++ tail) : x = y ∧ rest = tail := by
  have input : locatedInput ts (locatedInput rest s) = locatedInput us (locatedInput tail s) := by
    rw [← locatedInput_append, ← locatedInput_append, he]
  have px := boolean_statements_coverage hx e (locatedInput rest s) fx
  have py := boolean_statements_coverage hy d (locatedInput tail s) fy
  have fuel : e + d + 6 = d + e + 6 := by omega
  rw [fuel, input] at px
  have pair := Except.ok.inj (px.symm.trans py)
  have suffix := congrArg (fun p => p.2.ts.map (fun t : Located => t.tok)) pair
  simp only [locatedInput, List.map_append, List.map_map, Function.comp_def, atToken,
    List.map_id'] at suffix
  exact ⟨congrArg Prod.fst pair, List.append_cancel_right suffix⟩

#print axioms boolean_statements_prefix_unique
#print axioms boolean_loops_closed
#print axioms boolean_statements_node
#print axioms boolean_statements_nearest_else
#print axioms boolean_statements_yield
#print axioms boolean_statements_token_unique
#print axioms boolean_statements_derives_iff
#print axioms boolean_statements_yield_unique
end Solidity.Frontend.StatementGrammarH28
