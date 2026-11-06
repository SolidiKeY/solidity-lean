import Solidity.Frontend.StatementGrammarH28.BoolCompound

/-! Arbitrarily nested Boolean loops over the recursive block/control fragment.
The relation indexes existing intrinsic syntax, actual tokens and a structural
fuel budget. Expressions are fixed Boolean atoms. No general expression or
conditional uniqueness, source validity, or compiler correctness is claimed. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

inductive BooleanLoops : {k : SCtx} → Syn (.stmt k) → List Tok → Nat → Prop where
  | block {k : SCtx} {xs : Syn (.list (.item k))} {ts : List Tok} {d : Nat} :
      NestedItems xs ts d → BooleanLoops (.blockStmt (.block xs)) (braces ts) d
  | whileLoop {l u b : Bool} {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} {d : Nat} :
      BooleanLoops x ts d → BooleanLoops (Syn.whileStmt (l := l) (.lit (.bool b)) x)
        ([.kw .while_, .punct .lparen, .bool b, .punct .rparen] ++ ts) (d + 1)
  | forLoop {l u : Bool} {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} {d : Nat} :
      BooleanLoops x ts d → BooleanLoops (Syn.forStmt (l := l) .none .none .none x)
        ([.kw .for_, .punct .lparen, .punct .semi, .punct .semi, .punct .rparen] ++ ts) (d + 1)
  | doLoop {l u b : Bool} {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} {d : Nat} :
      BooleanLoops x ts d → BooleanLoops (Syn.doWhile (l := l) x (.lit (.bool b)))
        ([.kw .do_] ++ ts ++ [.kw .while_, .punct .lparen, .bool b, .punct .rparen, .punct .semi]) (d + 1)

/-- Coverage at every excess fuel, derived from the intrinsic witness. -/
theorem boolean_loops_coverage {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok} {d : Nat}
    (h : BooleanLoops x ts d) (n : Nat) (s : St) :
    stmt (n + d + 6) k (locatedInput ts s) = .ok (x, s) := by
  induction h generalizing n s with
  | @block k xs ts d h =>
    have hb := nested_block_stmt_coverage h (n + 1) s
    have hf : n + 1 + d + 5 = n + d + 6 := by omega
    rw [hf] at hb
    exact hb
  | @whileLoop l u b x ts d h ih =>
    rw [locatedInput_append]
    change stmt ((n + d + 1) + 6) ⟨l, u⟩
      (conditionInput .while_ b (locatedInput ts s)) = _
    rw [while_bool_prefix]
    have hf : n + d + 1 + 5 = n + d + 6 := by omega
    rw [hf, ih]
    rfl
  | @forLoop l u x ts d h ih =>
    rw [locatedInput_append, stmt]
    change (stmt (n + (d + 1) + 5) ⟨true, u⟩ (locatedInput ts s)).bind
      (fun p => .ok (Syn.forStmt (l := l) .none .none .none p.1, p.2)) = _
    have hf : n + (d + 1) + 5 = n + d + 6 := by omega
    rw [hf, ih]
    rfl
  | @doLoop l u b x ts d h ih =>
    rw [locatedInput_append, locatedInput_append, stmt]
    change (stmt (n + (d + 1) + 5) ⟨true, u⟩
      (locatedInput ts (doTail b s))).bind (fun p =>
        ((do expect (.kw .while_) "'while'"
             expectP .lparen
             let c ← expr (n + (d + 1) + 5)
             expectP .rparen
             expectP .semi
             pure (Syn.doWhile (l := l) p.1 c)) : P (Syn (.stmt ⟨l, u⟩))) p.2) = _
    have hf : n + (d + 1) + 5 = n + d + 6 := by omega
    rw [hf, ih]
    change (expr ((n + d + 1) + 5) (boolBefore b .rparen (punctBefore .semi s))).bind
      (fun p =>
        ((do expectP .rparen
             expectP .semi
             pure (Syn.doWhile (l := l) x p.1)) : P (Syn (.stmt ⟨l, u⟩))) p.2) = _
    rw [bool_expr_rparen]
    rfl

/-- Actual printer computation, for arbitrary layouts; this fragment uses none. -/
theorem boolean_loops_yield {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok} {d : Nat}
    (h : BooleanLoops x ts d) (L : List Choice) : x.yield L = some ([ts], L) := by
  induction h with
  | block h =>
    rw [Syn.yield, nested_block_yield h L]
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

/-- Equality is recovered with a common, proved sufficient fuel budget. -/
theorem boolean_loops_token_unique {k : SCtx} {x y : Syn (.stmt k)}
    {ts us : List Tok} {d e : Nat} (hx : BooleanLoops x ts d) (hy : BooleanLoops y us e)
    (he : ts = us) : x = y := by
  subst us
  let s : St := ⟨[], [], 0⟩
  have px := boolean_loops_coverage hx e s
  have py := boolean_loops_coverage hy d s
  have hf : e + d + 6 = d + e + 6 := by omega
  rw [hf] at px
  exact congrArg Prod.fst (Except.ok.inj (px.symm.trans py))

theorem boolean_loops_derives_iff {k : SCtx} {x : Syn (.stmt k)}
    {ts : List Tok} {d : Nat} (h : BooleanLoops x ts d) (words : List Tok) :
    x.Derives words ↔ words = ts := by
  constructor
  · intro ⟨L, hy⟩
    unfold Syn.toks at hy
    rw [boolean_loops_yield h L] at hy
    cases L with
    | nil =>
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hy
      exact (Option.some.inj hy).symm
    | cons choice rest => cases hy
  · intro he
    subst words
    refine ⟨[], ?_⟩
    unfold Syn.toks
    rw [boolean_loops_yield h []]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

/-- Unconditional yield uniqueness inside this indexed loop fragment only. -/
theorem boolean_loops_yield_unique {k : SCtx} {x y : Syn (.stmt k)}
    {ts us words : List Tok} {d e : Nat} (hx : BooleanLoops x ts d)
    (hy : BooleanLoops y us e) (dx : x.Derives words) (dy : y.Derives words) : x = y := by
  exact boolean_loops_token_unique hx hy
    (((boolean_loops_derives_iff hx words).mp dx).symm.trans
      ((boolean_loops_derives_iff hy words).mp dy))

#print axioms boolean_loops_coverage
#print axioms boolean_loops_yield
#print axioms boolean_loops_token_unique
#print axioms boolean_loops_derives_iff
#print axioms boolean_loops_yield_unique
end Solidity.Frontend.StatementGrammarH28
