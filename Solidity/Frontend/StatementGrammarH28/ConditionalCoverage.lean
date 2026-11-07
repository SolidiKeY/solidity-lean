import Solidity.Frontend.StatementGrammarH28.ConditionalPrefix

/-! Recursive Boolean conditionals and loops over the existing block/control
fragment. The else-bearing constructor retains exactly the existing closed
then-branch contract. Open statements require a suffix not starting in else;
closed statements preserve arbitrary suffixes. No general expression claim. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

inductive BooleanStatements : {k : SCtx} → Syn (.stmt k) → List Tok → Nat → Prop where
  | loops {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok} {d : Nat} :
      BooleanLoops x ts d → BooleanStatements x ts d
  | ifNone {k : SCtx} {b : Bool} {x : Syn (.stmt k)} {ts : List Tok} {d : Nat} :
      BooleanStatements x ts d → BooleanStatements (.ifStmt (.lit (.bool b)) x .none)
        ([.kw .if_, .punct .lparen, .bool b, .punct .rparen] ++ ts) (d + 1)
  | ifSome {k : SCtx} {b : Bool} {t e : Syn (.stmt k)} {ts es : List Tok} {d f : Nat} :
      BooleanStatements t ts d → BooleanStatements e es f → t.openIf = false →
      BooleanStatements (.ifStmt (.lit (.bool b)) t (.some e))
        ([.kw .if_, .punct .lparen, .bool b, .punct .rparen] ++ ts ++ [.kw .else_] ++ es) (d + f + 1)
  | whileLoop {l u b : Bool} {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} {d : Nat} :
      BooleanStatements x ts d → BooleanStatements (Syn.whileStmt (l := l) (.lit (.bool b)) x)
        ([.kw .while_, .punct .lparen, .bool b, .punct .rparen] ++ ts) (d + 1)
  | forLoop {l u : Bool} {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} {d : Nat} :
      BooleanStatements x ts d → BooleanStatements (Syn.forStmt (l := l) .none .none .none x)
        ([.kw .for_, .punct .lparen, .punct .semi, .punct .semi, .punct .rparen] ++ ts) (d + 1)
  | doLoop {l u b : Bool} {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} {d : Nat} :
      BooleanStatements x ts d → BooleanStatements (Syn.doWhile (l := l) x (.lit (.bool b)))
        ([.kw .do_] ++ ts ++ [.kw .while_, .punct .lparen, .bool b, .punct .rparen, .punct .semi]) (d + 1)

/-- Open-if syntax must not be followed by an else owned by another statement. -/
def StatementFrame {k : SCtx} (x : Syn (.stmt k)) (s : St) : Prop :=
  x.openIf = false ∨ NoFollowingElse s

theorem boolean_statements_coverage {k : SCtx} {x : Syn (.stmt k)}
    {ts : List Tok} {d : Nat} (h : BooleanStatements x ts d) (n : Nat) (s : St)
    (hf : StatementFrame x s) :
    stmt (n + d + 6) k (locatedInput ts s) = .ok (x, s) := by
  induction h generalizing n s with
  | loops h => exact boolean_loops_coverage h n s
  | @ifNone k b x ts d h ih =>
    have he : NoFollowingElse s := by
      rcases hf with hc | he
      · cases hc
      · exact he
    have hb := ih n s (Or.inr he)
    rw [locatedInput_append]
    change stmt ((n + d + 1) + 6) k (conditionInput .if_ b (locatedInput ts s)) = _
    rw [if_bool_prefix]
    have fuel : n + d + 1 + 5 = n + d + 6 := by omega
    change (stmt (n + d + 1 + 5) k (locatedInput ts s)).bind (fun p =>
      ((do if ← eat (.kw .else_) then
             return Syn.ifStmt (.lit (.bool b)) p.1 (.some (← stmt (n + d + 1 + 5) k))
           else return Syn.ifStmt (.lit (.bool b)) p.1 .none) : P (Syn (.stmt k))) p.2) = _
    rw [fuel, hb]
    change (eat (.kw .else_) s).bind (fun p =>
      ((if p.1 then do
          return Syn.ifStmt (.lit (.bool b)) x (.some (← stmt (n + d + 6) k))
        else pure (Syn.ifStmt (.lit (.bool b)) x .none)) : P (Syn (.stmt k))) p.2) = _
    rw [eat_else_false s he]
    rfl
  | @ifSome k b t e ts es d f ht he hc iht ihe =>
    let tail := locatedInput [.kw .else_] (locatedInput es s)
    have pt := iht (n + f) tail (Or.inl hc)
    have pe := ihe (n + d) s hf
    have ft : n + f + d + 6 = n + (d + f) + 6 := by omega
    have fe : n + d + f + 6 = n + (d + f) + 6 := by omega
    rw [ft] at pt
    rw [fe] at pe
    rw [locatedInput_append, locatedInput_append, locatedInput_append]
    change stmt ((n + (d + f) + 1) + 6) k
      (conditionInput .if_ b (locatedInput ts tail)) = _
    rw [if_bool_prefix]
    have fuel : n + (d + f) + 1 + 5 = n + (d + f) + 6 := by omega
    change (stmt (n + (d + f) + 1 + 5) k (locatedInput ts tail)).bind (fun p =>
      ((do if ← eat (.kw .else_) then
             return Syn.ifStmt (.lit (.bool b)) p.1 (.some (← stmt (n + (d + f) + 1 + 5) k))
           else return Syn.ifStmt (.lit (.bool b)) p.1 .none) : P (Syn (.stmt k))) p.2) = _
    rw [fuel, pt]
    change (stmt (n + (d + f) + 6) k (locatedInput es s)).bind
      (fun p => .ok (Syn.ifStmt (.lit (.bool b)) t (.some p.1), p.2)) = _
    rw [pe]
    rfl
  | @whileLoop l u b x ts d h ih =>
    rw [locatedInput_append]
    change stmt ((n + d + 1) + 6) ⟨l, u⟩
      (conditionInput .while_ b (locatedInput ts s)) = _
    rw [while_bool_prefix]
    have fuel : n + d + 1 + 5 = n + d + 6 := by omega
    rw [fuel, ih n s hf]
    rfl
  | @forLoop l u x ts d h ih =>
    rw [locatedInput_append, stmt]
    change (stmt (n + (d + 1) + 5) ⟨true, u⟩ (locatedInput ts s)).bind
      (fun p => .ok (Syn.forStmt (l := l) .none .none .none p.1, p.2)) = _
    have fuel : n + (d + 1) + 5 = n + d + 6 := by omega
    rw [fuel, ih n s hf]
    rfl
  | @doLoop l u b x ts d h ih =>
    have frame : StatementFrame x (doTail b s) := Or.inr (by intro bad; cases bad)
    rw [locatedInput_append, locatedInput_append, stmt]
    change (stmt (n + (d + 1) + 5) ⟨true, u⟩
      (locatedInput ts (doTail b s))).bind (fun p =>
        ((do expect (.kw .while_) "'while'"
             expectP .lparen
             let c ← expr (n + (d + 1) + 5)
             expectP .rparen
             expectP .semi
             pure (Syn.doWhile (l := l) p.1 c)) : P (Syn (.stmt ⟨l, u⟩))) p.2) = _
    have fuel : n + (d + 1) + 5 = n + d + 6 := by omega
    rw [fuel, ih n (doTail b s) frame]
    change (expr ((n + d + 1) + 5) (boolBefore b .rparen (punctBefore .semi s))).bind
      (fun p =>
        ((do expectP .rparen
             expectP .semi
             pure (Syn.doWhile (l := l) x p.1)) : P (Syn (.stmt ⟨l, u⟩))) p.2) = _
    rw [bool_expr_rparen]
    rfl

#print axioms boolean_statements_coverage
end Solidity.Frontend.StatementGrammarH28
