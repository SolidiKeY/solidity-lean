import Solidity.Goals.ElabTotal

namespace Solidity.Goals

open Solidity

/--
info: open Solidity.Goals.elabKernelTotal ← Solidity.elabKernel_total plan et3-elab-knot-total
-/
#guard_msgs in
#roadmap_goal elabKernelTotal

section Controls

variable [FreshNames] (C : Contract)

/-- A knot that always fails does not satisfy the equations: its block of no
statements fails where the knot's elaborates to nothing. -/
example : ¬ ElabKernelFix C (default : ElabRec C) := fun ⟨h, _⟩ => by
  have := congrArg (fun x => ((x.run { funs := [] }).run ([], 0)).run {}) h
  nomatch this

/-- A knot whose block drops its statements' programs (`elabStmtsP` as
`pure []` everywhere) breaks the cons equation at a failing statement. -/
example (rc : ElabRec C) (hP : ∀ s, rc.elabStmtP s = throw "x")
    (hL : ∀ ss, rc.elabStmtsP ss = pure []) : ¬ ElabKernelFix C rc := fun ⟨_, h, _⟩ => by
  have := congrArg (fun x => ((x.run { funs := [] }).run ([], 0)).run {}) (h .brk [])
  simp only [hP, hL] at this
  nomatch this

/-- Clause 1 gives the public equations. -/
example (h : elabKernelTotal) :
    elabStmtsP C [] = pure [] ∧
    (∀ s ss, elabStmtsP C (s :: ss) = do
      let P ← elabStmtP C s
      let Q ← elabStmtsP C ss
      pure (P ++ Q)) ∧
    elabStmtP C = elabStmtPWith C (elabRec C ()) ∧
    elabStmt1 C = elabStmt1With C (elabRec C ()) ∧
    hoistStmt C = hoistStmtWith C (elabRec C ()) ∧
    hoist C = hoistWith C (elabRec C ()) := by
  obtain ⟨⟨h0, h1, hP, h1', hS, hH⟩, n, -⟩ := h.1 C
  obtain ⟨nH, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, nS, nP, n1, -, -, nL, -⟩ := n
  refine ⟨nL ▸ h0, fun s ss => ?_, nP ▸ hP, n1 ▸ h1', nS ▸ hS, nH ▸ hH⟩
  rw [← nL, ← nP]; exact h1 s ss

end Controls

/-- The `RawExpr.mapM` side condition is needed: a callback that wraps its
argument has no fixpoint (`x = .unop .neg x` has no solution). -/
example : ∀ x : RawExpr, x ≠ .unop .neg x := by
  intro x h; have := congrArg sizeOf h; simp at this

end Solidity.Goals
