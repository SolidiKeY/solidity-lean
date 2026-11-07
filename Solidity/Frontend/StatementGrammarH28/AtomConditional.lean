import Solidity.Frontend.StatementGrammarH28.ConditionalYield

/-! Conditional and loop framing with arbitrary expression conditions.

The conditions of `if`, `while` and `do … while` are read-only expression
atoms. Their parse is the exposed premise `ExprAtomRparen`: the atom's tokens
parse back to exactly that expression before a closing parenthesis, at every
fuel above a stated budget, leaving the parenthesis unread. The premise is
proved here only for Boolean literals and identifiers; expression parser
completeness and expression uniqueness (SOL-EU) belong to the expression
lanes and are not claimed. The else-bearing constructor keeps exactly the
existing closed-then contract (`if_some_contract_iff`). -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- Exposed expression-atom premise before `)`, with fuel budget `a`. -/
def ExprAtomRparen (e : Syn .expr) (es : List Tok) (a : Nat) : Prop :=
  ∀ (n : Nat) (s : St),
    expr (n + a) (locatedInput (es ++ [.punct .rparen]) s) = .ok (e, punctBefore .rparen s)

theorem bool_atom_rparen (b : Bool) : ExprAtomRparen (.lit (.bool b)) [.bool b] 5 :=
  fun n s => bool_expr_rparen n b s

theorem ident_atom_rparen (x : String) : ExprAtomRparen (.ident x) [.ident x] 5 :=
  fun _ _ => rfl

/-- Statements over the Boolean fragment closed under `if`, `while` and
`do … while` with arbitrary atom conditions and the empty-header `for`. -/
inductive AtomStatements : {k : SCtx} → Syn (.stmt k) → List Tok → Nat → Prop where
  | boolean {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok} {d : Nat} :
      BooleanStatements x ts d → AtomStatements x ts d
  | ifNone {k : SCtx} {c : Syn .expr} {cs : List Tok} {a : Nat}
      {x : Syn (.stmt k)} {ts : List Tok} {d : Nat} :
      ExprAtomRparen c cs a → AtomStatements x ts d →
      AtomStatements (.ifStmt c x .none)
        ([.kw .if_, .punct .lparen] ++ cs ++ [.punct .rparen] ++ ts) (d + a + 1)
  | ifSome {k : SCtx} {c : Syn .expr} {cs : List Tok} {a : Nat}
      {t e : Syn (.stmt k)} {ts es : List Tok} {d f : Nat} :
      ExprAtomRparen c cs a → AtomStatements t ts d → AtomStatements e es f →
      t.openIf = false →
      AtomStatements (.ifStmt c t (.some e))
        ([.kw .if_, .punct .lparen] ++ cs ++ [.punct .rparen] ++ ts ++ [.kw .else_] ++ es)
        (d + f + a + 1)
  | whileLoop {l u : Bool} {c : Syn .expr} {cs : List Tok} {a : Nat}
      {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} {d : Nat} :
      ExprAtomRparen c cs a → AtomStatements x ts d →
      AtomStatements (Syn.whileStmt (l := l) c x)
        ([.kw .while_, .punct .lparen] ++ cs ++ [.punct .rparen] ++ ts) (d + a + 1)
  | forLoop {l u : Bool} {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} {d : Nat} :
      AtomStatements x ts d → AtomStatements (Syn.forStmt (l := l) .none .none .none x)
        ([.kw .for_, .punct .lparen, .punct .semi, .punct .semi, .punct .rparen] ++ ts) (d + 1)
  | doLoop {l u : Bool} {c : Syn .expr} {cs : List Tok} {a : Nat}
      {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} {d : Nat} :
      ExprAtomRparen c cs a → AtomStatements x ts d →
      AtomStatements (Syn.doWhile (l := l) x c)
        ([.kw .do_] ++ ts ++ [.kw .while_, .punct .lparen] ++ cs ++ [.punct .rparen, .punct .semi])
        (d + a + 1)

/-- The `if` header with an atom condition, before its body is parsed. -/
theorem if_atom_prefix {c : Syn .expr} {cs : List Tok} {a : Nat}
    (hc : ExprAtomRparen c cs a) (n : Nat) (k : SCtx) (s : St) :
    stmt (n + a + 1) k (locatedInput ([.kw .if_, .punct .lparen] ++ cs ++ [.punct .rparen]) s) =
      ((do let body ← stmt (n + a) k
           if ← eat (.kw .else_) then
             return Syn.ifStmt c body (.some (← stmt (n + a) k))
           else return Syn.ifStmt c body .none) : P (Syn (.stmt k))) s := by
  rw [stmt]
  change (expr (n + a) (locatedInput (cs ++ [.punct .rparen]) s)).bind (fun p =>
    ((do expectP .rparen
         let body ← stmt (n + a) k
         if ← eat (.kw .else_) then
           return Syn.ifStmt p.1 body (.some (← stmt (n + a) k))
         else return Syn.ifStmt p.1 body .none) : P (Syn (.stmt k))) p.2) = _
  rw [hc n s]
  rfl

/-- The `while` header with an atom condition. -/
theorem while_atom_prefix {c : Syn .expr} {cs : List Tok} {a : Nat}
    (hc : ExprAtomRparen c cs a) (n : Nat) (l u : Bool) (s : St) :
    stmt (n + a + 1) ⟨l, u⟩
        (locatedInput ([.kw .while_, .punct .lparen] ++ cs ++ [.punct .rparen]) s) =
      (stmt (n + a) ⟨true, u⟩ s).bind
        (fun p => .ok (Syn.whileStmt (l := l) c p.1, p.2)) := by
  rw [stmt]
  change (expr (n + a) (locatedInput (cs ++ [.punct .rparen]) s)).bind (fun p =>
    ((do expectP .rparen
         let body ← stmt (n + a) ⟨true, u⟩
         pure (Syn.whileStmt (l := l) p.1 body)) : P (Syn (.stmt ⟨l, u⟩))) p.2) = _
  rw [hc n s]
  rfl

/-- The `do … while` tail with an atom condition. -/
theorem do_atom_tail {c : Syn .expr} {cs : List Tok} {a : Nat}
    (hc : ExprAtomRparen c cs a) (n : Nat) (l u : Bool) (x : Syn (.stmt ⟨true, u⟩)) (s : St) :
    ((do expect (.kw .while_) "'while'"
         expectP .lparen
         let c' ← expr (n + a)
         expectP .rparen
         expectP .semi
         pure (Syn.doWhile (l := l) x c')) : P (Syn (.stmt ⟨l, u⟩)))
      (locatedInput ([.kw .while_, .punct .lparen] ++ cs ++ [.punct .rparen, .punct .semi]) s) =
      .ok (Syn.doWhile (l := l) x c, s) := by
  have hs := hc n (punctBefore .semi s)
  have hi : locatedInput ([.kw .while_, .punct .lparen] ++ cs ++ [.punct .rparen, .punct .semi]) s =
      locatedInput [.kw .while_, .punct .lparen]
        (locatedInput (cs ++ [.punct .rparen]) (punctBefore .semi s)) := by
    simp only [punctBefore, ← locatedInput_append, List.append_assoc, List.cons_append,
      List.nil_append]
  rw [hi]
  change (expr (n + a) (locatedInput (cs ++ [.punct .rparen]) (punctBefore .semi s))).bind
    (fun p =>
      ((do expectP .rparen
           expectP .semi
           pure (Syn.doWhile (l := l) x p.1)) : P (Syn (.stmt ⟨l, u⟩))) p.2) = _
  rw [hs]
  rfl

/-- Coverage at every excess fuel and every framed suffix, derived from the
intrinsic witness and the exposed atom premises only. -/
theorem atom_statements_coverage {k : SCtx} {x : Syn (.stmt k)}
    {ts : List Tok} {d : Nat} (h : AtomStatements x ts d) (n : Nat) (s : St)
    (hf : StatementFrame x s) :
    stmt (n + d + 6) k (locatedInput ts s) = .ok (x, s) := by
  induction h generalizing n s with
  | boolean h => exact boolean_statements_coverage h n s hf
  | @ifNone k c cs a x ts d hc h ih =>
    have he : NoFollowingElse s := by
      rcases hf with hc' | he
      · cases hc'
      · exact he
    have hb := ih (n + a) s (Or.inr he)
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
  | @ifSome k c cs a t e ts es d f hc ht he hcl iht ihe =>
    let tail := locatedInput [.kw .else_] (locatedInput es s)
    have pt := iht (n + f + a) tail (Or.inl hcl)
    have pe := ihe (n + d + a) s hf
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
  | @whileLoop l u c cs a x ts d hc h ih =>
    rw [locatedInput_append]
    have fuel : n + (d + a + 1) + 6 = (n + d + 6) + a + 1 := by omega
    rw [fuel, while_atom_prefix hc]
    have fb : n + d + 6 + a = n + a + d + 6 := by omega
    rw [fb, ih (n + a) s hf]
    rfl
  | @forLoop l u x ts d h ih =>
    rw [locatedInput_append, stmt]
    change (stmt (n + (d + 1) + 5) ⟨true, u⟩ (locatedInput ts s)).bind
      (fun p => .ok (Syn.forStmt (l := l) .none .none .none p.1, p.2)) = _
    have fuel : n + (d + 1) + 5 = n + d + 6 := by omega
    rw [fuel, ih n s hf]
    rfl
  | @doLoop l u c cs a x ts d hc h ih =>
    let tail := locatedInput ([.kw .while_, .punct .lparen] ++ cs ++
      [.punct .rparen, .punct .semi]) s
    have frame : StatementFrame x tail := Or.inr (by intro bad; cases bad)
    have hb := ih (n + a) tail frame
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

/-- The root keeps the immutable precedence node contract. -/
theorem atom_statements_node {k : SCtx} {x : Syn (.stmt k)}
    {ts : List Tok} {d : Nat} (h : AtomStatements x ts d) : x.precNode = true := by
  cases h with
  | boolean h => exact boolean_statements_node h
  | ifNone => rfl
  | ifSome _ _ _ hc => exact (if_some_contract_iff _ _ _).mpr hc
  | whileLoop => rfl
  | forLoop => rfl
  | doLoop => rfl

/-- Nearest else: an else-bearing atom conditional has no open then-spine. -/
theorem atom_statements_nearest_else {k : SCtx} {c : Syn .expr} {t e : Syn (.stmt k)}
    {ts : List Tok} {d : Nat} (h : AtomStatements (.ifStmt c t (.some e)) ts d) :
    ¬ OpenSpine t :=
  nearestElse_node _ _ _ (atom_statements_node h)

/-- Token uniqueness inside the fragment, from the parser being a function:
two witnesses over the same tokens are the same tree. The atoms enter only
through their exposed premises; no expression yield injectivity is assumed. -/
theorem atom_statements_token_unique {k : SCtx} {x y : Syn (.stmt k)}
    {ts us : List Tok} {d e : Nat} (hx : AtomStatements x ts d)
    (hy : AtomStatements y us e) (he : ts = us) : x = y := by
  subst us
  let s : St := ⟨[], [], 0⟩
  have frame (z : Syn (.stmt k)) : StatementFrame z s := Or.inr (by intro bad; cases bad)
  have px := atom_statements_coverage hx e s (frame x)
  have py := atom_statements_coverage hy d s (frame y)
  have hf : e + d + 6 = d + e + 6 := by omega
  rw [hf] at px
  exact congrArg Prod.fst (Except.ok.inj (px.symm.trans py))

/-- Every Boolean witness is an atom witness with the same budget. -/
theorem atom_statements_of_boolean {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok} {d : Nat}
    (h : BooleanStatements x ts d) : AtomStatements x ts d := .boolean h

#print axioms bool_atom_rparen
#print axioms ident_atom_rparen
#print axioms if_atom_prefix
#print axioms while_atom_prefix
#print axioms do_atom_tail
#print axioms atom_statements_coverage
#print axioms atom_statements_node
#print axioms atom_statements_nearest_else
#print axioms atom_statements_token_unique
end Solidity.Frontend.StatementGrammarH28
