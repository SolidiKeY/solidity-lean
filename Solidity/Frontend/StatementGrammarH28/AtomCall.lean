import Solidity.Frontend.StatementGrammarH28.AtomSimple

/-! `emit` and `revert` statements over stated atom premises.

The event or error path enters through `PathAtom` (the existing `pathExpr`
parser reads exactly that path before an argument list's `(`), and the
arguments through `ArgsAtom` (the existing `callArgs` parser reads exactly
those arguments before `;`). Both are proved here for identifiers and the
empty positional argument list only; no expression completeness or
expression uniqueness (SOL-EU) is claimed. `revert` is contextual: the
statement dispatcher takes it only when the next token is an identifier. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- The path premise: `pathExpr` reads `ps` as `e` and stops at `(`. -/
def PathAtom (e : Syn .expr) (ps : List Tok) : Prop :=
  ∀ (rest : List Tok) (s : St), rest.head? = some (.punct .lparen) →
    pathExpr (locatedInput (ps ++ rest) s) = .ok (e, locatedInput rest s)

/-- The argument premise before `;`, with fuel budget `b`. -/
def ArgsAtom (args : Syn .callArgs) (as : List Tok) (b : Nat) : Prop :=
  ∀ (n : Nat) (s : St),
    callArgs (n + b) (locatedInput (as ++ [.punct .semi]) s) = .ok (args, punctBefore .semi s)

theorem ident_path_atom (x : String) : PathAtom (.ident x) [.ident x] := by
  intro rest s h
  cases rest with
  | nil => cases h
  | cons t tail =>
    cases h
    rfl

theorem empty_args_atom : ArgsAtom (.positional .nil) [.punct .lparen, .punct .rparen] 1 :=
  fun _ _ => rfl

/-- `emit E(args);` from the premises. -/
theorem emit_step {k : SCtx} {e : Syn .expr} {ps : List Tok} {args : Syn .callArgs}
    {as : List Tok} {b : Nat} (hp : PathAtom e ps) (ha : ArgsAtom args as b)
    (hl : as.head? = some (.punct .lparen)) (m : Nat) (s : St) :
    stmt (m + b + 1) k (locatedInput ([.kw .emit] ++ ps ++ as ++ [.punct .semi]) s) =
      .ok (.emit e args, s) := by
  have hi : locatedInput ([.kw .emit] ++ ps ++ as ++ [.punct .semi]) s =
      locatedInput [.kw .emit] (locatedInput (ps ++ (as ++ [.punct .semi])) s) := by
    simp only [← locatedInput_append, List.append_assoc]
  have hh : (as ++ [Tok.punct .semi]).head? = some (Tok.punct .lparen) := by
    cases as with
    | nil => cases hl
    | cons t tail => exact hl
  rw [hi, stmt]
  change (pathExpr (locatedInput (ps ++ (as ++ [.punct .semi])) s)).bind (fun p =>
    ((do let a ← callArgs (m + b)
         expectP .semi
         return Syn.emit p.1 a) : P (Syn (.stmt k))) p.2) = _
  rw [hp _ s hh]
  change (callArgs (m + b) (locatedInput (as ++ [.punct .semi]) s)).bind (fun p =>
    ((do expectP .semi
         return Syn.emit e p.1) : P (Syn (.stmt k))) p.2) = _
  rw [ha m s]
  rfl

/-- `revert E(args);` from the premises; the path starts with an identifier. -/
theorem revert_step {k : SCtx} {e : Syn .expr} {y : String} {ps : List Tok}
    {args : Syn .callArgs} {as : List Tok} {b : Nat} (hp : PathAtom e (.ident y :: ps))
    (ha : ArgsAtom args as b) (hl : as.head? = some (.punct .lparen)) (m : Nat) (s : St) :
    stmt (m + b + 1) k
      (locatedInput ([.ident "revert"] ++ (.ident y :: ps) ++ as ++ [.punct .semi]) s) =
      .ok (.revert e args, s) := by
  have hi : locatedInput ([.ident "revert"] ++ (.ident y :: ps) ++ as ++ [.punct .semi]) s =
      locatedInput [.ident "revert"] (locatedInput (.ident y :: ps ++ (as ++ [.punct .semi])) s) := by
    simp only [← locatedInput_append, List.append_assoc, List.cons_append]
  have hh : (as ++ [Tok.punct .semi]).head? = some (Tok.punct .lparen) := by
    cases as with
    | nil => cases hl
    | cons t tail => exact hl
  rw [hi, stmt]
  change (pathExpr (locatedInput (.ident y :: ps ++ (as ++ [.punct .semi])) s)).bind (fun p =>
    ((do let a ← callArgs (m + b)
         expectP .semi
         return Syn.revert p.1 a) : P (Syn (.stmt k))) p.2) = _
  rw [hp _ s hh]
  change (callArgs (m + b) (locatedInput (as ++ [.punct .semi]) s)).bind (fun p =>
    ((do expectP .semi
         return Syn.revert e p.1) : P (Syn (.stmt k))) p.2) = _
  rw [ha m s]
  rfl

#print axioms ident_path_atom
#print axioms empty_args_atom
#print axioms emit_step
#print axioms revert_step

/-- The token after a contextual `revert` is not an identifier, so the
statement dispatcher reads an expression statement (`revert(...)`, `revert;`,
`revert = …`, …) rather than a `revert` statement. -/
def revertExprNext : List Tok → Bool
  | .ident _ :: _ => false
  | _ => true

theorem revert_expr_dispatch (m : Nat) (k : SCtx) (t : Tok) (rest : List Tok) (s : St)
    (h : revertExprNext (t :: rest) = true) :
    stmt (m + 1) k (locatedInput (.ident "revert" :: t :: rest) s) =
      simpleStmt m k (locatedInput (.ident "revert" :: t :: rest) s) := by
  cases t <;> first | rfl | cases h

/-- `revert …;` read as a simple statement, from the `simple` premise. -/
theorem revert_expr_coverage {k : SCtx} {x : Syn .simple} {ss : List Tok} {a : Nat}
    (hx : SimpleAtom x (.ident "revert" :: ss) a)
    (hr : revertExprNext (ss ++ [.punct .semi]) = true) (n : Nat) (s : St) :
    stmt (n + (a + 1) + 6) k (locatedInput (.ident "revert" :: ss ++ [.punct .semi]) s) =
      .ok (.simpleStmt x, s) := by
  obtain ⟨t, tail, ht⟩ : ∃ t tail, ss ++ [Tok.punct .semi] = t :: tail := by
    cases ss with
    | nil => exact ⟨_, _, rfl⟩
    | cons t tail => exact ⟨t, tail ++ [.punct .semi], rfl⟩
  have fuel : n + (a + 1) + 6 = (n + 5 + a + 1) + 1 := by omega
  rw [fuel, List.cons_append, ht, revert_expr_dispatch _ k t tail s (ht ▸ hr), ← ht,
    ← List.cons_append]
  change (simple (n + 5 + a) (locatedInput (.ident "revert" :: ss ++ [.punct .semi]) s)).bind
    (fun p => ((do expectP .semi; return Syn.simpleStmt p.1) : P (Syn (.stmt k))) p.2) = _
  rw [hx (n + 5) s]
  rfl

#print axioms revert_expr_dispatch
#print axioms revert_expr_coverage

end Solidity.Frontend.StatementGrammarH28
