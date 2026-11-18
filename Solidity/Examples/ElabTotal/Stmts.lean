import Solidity.Syntax.Elab.Stmt

/-!
# Checks: the block's two equations

`elabStmtsP` is total (`elabStmtsPWith` at the knot's `elabStmtP`), so a
block of two statements unfolds by `elabStmtsP_cons` twice and
`elabStmtsP_nil` once, with no `native_decide`; the per-statement producer
`elabStmtP` stays opaque (partial). The elaborator's run on a concrete
two-statement block agrees with the unfolded form, state included.
-/

namespace Solidity.Examples.ElabTotal.Stmts

open Solidity

variable [FreshNames]

/-- Two statements: the head, the second, the empty rest, concatenated. -/
theorem elabStmtsP_two (C : Contract) (s₁ s₂ : RawStmt) :
    elabStmtsP C [s₁, s₂] = (do
      let P ← elabStmtP C s₁
      let Q ← (do
        let P' ← elabStmtP C s₂
        let Q' ← pure []
        pure (P' ++ Q'))
      pure (P ++ Q)) := by
  rw [elabStmtsP_cons, elabStmtsP_cons, elabStmtsP_nil]

/-- The same unfolding through `runFrom`, the form downstream proofs read. -/
theorem elabStmtsP_two_runFrom (C : Contract) (s₁ s₂ : RawStmt)
    (sc : ElabScope) (st : ECtx × Nat) :
    (elabStmtsP C [s₁, s₂]).runFrom sc st =
      (do
        let P ← elabStmtP C s₁
        let Q ← elabStmtP C s₂
        pure (P ++ Q ++ [])).runFrom sc st := by
  rw [elabStmtsP_cons, elabStmtsP_cons, elabStmtsP_nil]
  simp only [bind_pure_comp, map_pure, bind_pure, List.append_nil]

private def C0 : Contract := { vars := [] }

/-- `uint x = 1; x = 2;`. -/
private def s₁ : RawStmt := .decl (.named "uint") "x" (some (.num 1))
private def s₂ : RawStmt := .assign (.name "x") (.num 2)

/-- The run's statement count and final locals, or its error. -/
private def summary (x : ElabM (SProg C0)) : Option (Nat × List String × Nat) :=
  ((x.runFrom { funs := [] } ([], 1)).map fun (P, (Γ, k)) => (P.length, Γ.map (·.1), k)).toOption

-- The block elaborates, and agrees with its statements run one after the other.
#guard summary (elabStmtsP C0 [s₁, s₂]) == some (2, ["x"], 1)
#guard summary (elabStmtsP C0 [s₁, s₂]) ==
  summary (do let P ← elabStmtP C0 s₁; let Q ← elabStmtP C0 s₂; pure (P ++ Q))
#guard summary (elabStmtsP C0 []) == some (0, [], 1)

-- Standard axioms only, no `native_decide`.
/-- info: 'Solidity.elabStmtsP_nil' depends on axioms: [propext] -/
#guard_msgs in #print axioms elabStmtsP_nil

/-- info: 'Solidity.elabStmtsP_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms elabStmtsP_cons

/--
info: 'Solidity.Examples.ElabTotal.Stmts.elabStmtsP_two_runFrom' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms elabStmtsP_two_runFrom

end Solidity.Examples.ElabTotal.Stmts
