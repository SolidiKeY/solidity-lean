import Solidity.Correctness.Lowering.Sim.Match.Cases

/-!
# The expression cases: their strength (ls2-expressions)

`Sim.ExprCases` (`Sim/Match/Cases.lean`) is not proved here. This module
proves what it implies, which is why no arm-by-arm proof of it exists.

`RecSim` constrains five fields of the callback record. The arm
`hoistStmtWith` of a declaration `T x = e` (`e` not a call) returns the
captures of `rc.hoistTop e`, a field `RecSim` does not constrain. At the record
`passRec C P st'` (the five constrained callbacks fail, `hoistTop` returns `P`
and sets the state to `st'`) `RecSim` holds vacuously and that arm's output is
`P` at `st'`, for every `P` and `st'`. So the third conjunct of `ExprCases`
gives `SiteSim C raw sc st P st'` for every run (`sites_of_exprCases`): the
per-run obligation at every associated production body of the fragment,
loops, statements and state included, with no hypothesis left
(`runs_of_exprCases`), and so `diagram.Simulates` (`simulates_of_exprCases`).

## Limitations

* `expr_cases : ExprCases` is not proved, and by the above it is as hard as
  `diagram.Simulates`, which `Sim/Match.lean` documents as not provable as
  stated (`globRel` has no frame; `Diagram.Simulates` ranges over every Source
  frame). No counterexample to `ExprCases` is machine-checked: one needs a
  closed run of the `partial` elaborator.
* The same passthrough holds for `hoistWith` at `.binop` (`rc.hoistBinop`,
  with `narrowCapture`) and for `elabStmt1With` at `.unchecked` / `.checked`
  (`rc.elabBranch`); only the declaration arm is proved here.
-/
namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals (ElabRan elabKernelTotal)
open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)

variable [FreshNames]

/-- A record whose five constrained callbacks fail and whose `hoistTop`
returns the captures `P` and sets the state to `st'`. -/
def passRec (C : Contract) (P : SProg C) (st' : ECtx × Nat) : ElabRec C :=
  { (default : ElabRec C) with
    hoist := fun _ => throw ""
    hoistStmt := fun _ => throw ""
    elabStmtP := fun _ => throw ""
    elabStmt1 := fun _ => throw ""
    elabStmtsP := fun _ => throw ""
    hoistTop := fun e => do set st'; pure (P, e) }

/-- `RecSim` holds of `passRec`: its constrained callbacks have no successful run. -/
theorem passRec_sim (C : Contract) (P : SProg C) (st' : ECtx × Nat) :
    RecSim C (passRec C P st') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro a sc st b st'' ⟨m, m', ran⟩ <;> cases ran

/-- The declaration arm of `hoistStmtWith` at `passRec` returns `P` at `st'`,
from every scope and state. -/
theorem passRec_ran (C : Contract) (P : SProg C) (sc : ElabScope) (st st' : ECtx × Nat) :
    ElabRan (hoistStmtWith C (passRec C P st') (.decl (.named "") "" (some (.num 0)))) sc st
      (P, .decl (.named "") "" (some (.num 0))) st' :=
  ⟨default, default, rfl⟩

/-- **`ExprCases` gives the obligations at every site**, for every run. -/
theorem sites_of_exprCases (kernel : elabKernelTotal) (exprs : ExprCases) (C : Contract)
    (raw : List RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C) (st' : ECtx × Nat) :
    SiteSim C raw sc st P st' :=
  (exprs kernel C _ (passRec_sim C P st')).2.2.1 _ sc st _ st' (passRec_ran C P sc st st') raw

/-- **`ExprCases` alone gives the per-run part** of `diagram.Simulates`: no
statement case, state case or loop hypothesis is used. -/
theorem runs_of_exprCases (kernel : elabKernelTotal) (exprs : ExprCases) (b : Body) (u : Emitted)
    (m : ContextMap b.ctx u.Γ) (production : Production b u) (accepted : Accepted u)
    (assoc : diagram.Assoc b u m) : RunSim b u m := by
  obtain ⟨C, Γ, o⟩ := u
  obtain ⟨lowered, ⟨ran, placed⟩, threaded⟩ := production
  exact sites_of_exprCases kernel exprs C o.raw o.elabScope o.beforeElab.locals o.elaborated
    o.afterElab.locals b Γ o m ⟨rfl, rfl, rfl, rfl, rfl, ran, placed⟩ lowered threaded accepted assoc

/-- **`ExprCases` implies `diagram.Simulates`.** -/
theorem simulates_of_exprCases (kernel : elabKernelTotal) (exprs : ExprCases) :
    diagram.Simulates :=
  simulates_of_runs (runs_of_exprCases kernel exprs)

end Solidity.Correctness.Lowering.Sim
