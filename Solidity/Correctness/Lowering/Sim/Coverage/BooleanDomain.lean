import Solidity.Goals.LoweringDiagram

/-!
# The H1361 Boolean control domain

The syntax-defined domain selected for the H1184 restricted milestone toward
`Solidity.Goals.loweringBySimulation`. Membership contains no decoder-success,
association, production or acceptance premise. Decoder completeness and the
nonvacuous production receipt remain separate obligations.
-/
namespace Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain

open Solidity.Goals.Shrink.Lowering

/-- Boolean expressions over the caller's bound Boolean names. -/
inductive Expr (names : List String) : RawExpr → Prop where
  | name {x} : x ∈ names → Expr names (.name x)
  | bool (b) : Expr names (.bool b)
  | assign {x e} : x ∈ names → Expr names e → Expr names (.assign (.name x) e)
  | not {e} : Expr names e → Expr names (.unop .not e)
  | and {a b} : Expr names a → Expr names b → Expr names (.binop .and a b)
  | or {a b} : Expr names a → Expr names b → Expr names (.binop .or a b)
  | eq {a b} : Expr names a → Expr names b → Expr names (.binop .eqB a b)

mutual
  /-- Boolean control statements; `inside` permits abrupt exits only in loops. -/
  inductive Stmt (names : List String) : Bool → RawStmt → Prop where
    | assign {inside x e} : x ∈ names → Expr names e →
        Stmt names inside (.assign (.name x) e)
    | block {inside ss} : Stmts names inside ss → Stmt names inside (.block ss)
    | ite {inside c a b} : Expr names c → Stmts names inside a →
        Stmts names inside b → Stmt names inside (.ite c a b)
    | whileLoop {inside spec c ss} : Expr names c → Stmts names true ss →
        Stmt names inside (.whileLoop spec c ss)
    | brk : Stmt names true .brk
    | cont : Stmt names true .cont

  /-- Finite statement sequences, with no bound on their length or nesting. -/
  inductive Stmts (names : List String) : Bool → List RawStmt → Prop where
    | nil {inside} : Stmts names inside []
    | cons {inside s ss} : Stmt names inside s → Stmts names inside ss →
        Stmts names inside (s :: ss)
end

/-- The approved singleton-while boundary: a canonical checked empty contract
and scope, no return slots, full-width Boolean caller locals, and an empty
outer loop specification. Nested loop specifications are unrestricted, as in
the existing decoder spelling relation. The counter
and memo are unrestricted; production and acceptance remain separate. -/
def Input (b : Body) (u : Emitted) : Prop :=
  b.site = .loop ∧ u.C = { vars := [] } ∧ b.input.returnSlots = none ∧
  b.input.scope = { funs := [] } ∧
  ∃ (names : List String) (c : RawExpr) (ss : List RawStmt),
    b.input.before.locals.1 = names.map (fun x => (x, .val .bool)) ∧
    b.input.raw = [.whileLoop {} c ss] ∧ Expr names c ∧ Stmts names true ss

end Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain
