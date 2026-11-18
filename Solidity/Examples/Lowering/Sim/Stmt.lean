import Solidity.Correctness.Lowering.Sim.Stmt.Main

/-!
# The statement cases of the lowering diagram, used

The jump conjunct of `StmtCases` on concrete arms, `StmtCases` from the
conjuncts that remain, and the frame obstruction at a body.
-/
namespace Solidity.Examples.Lowering.Sim.Stmt

open Solidity.Goals (ElabRan ElabSat elabStmtsStep elabKernelTotal)
open Solidity.Goals.Shrink.Lowering
open Solidity.Correctness.Lowering.Sim

variable [FreshNames]

/-- `break;` through `elabStmtPWith`, at every record: its output meets the
obligations at its site (no body is elaborated to it). -/
example (kernel : elabKernelTotal) (C : Contract) (rc : ElabRec C) (sc : ElabScope)
    (st st' : ECtx × Nat) (P : SProg C) (ran : ElabRan (elabStmtPWith C rc .brk) sc st P st') :
    stmtQ C .brk sc st P st' :=
  (jump_cases C kernel rc).1 .brk rfl sc st P st' ran

/-- `return e;` through `elabStmt1With`, at every record. -/
example (kernel : elabKernelTotal) (C : Contract) (rc : ElabRec C) (e : RawExpr) :
    ∀ sc st P st', ElabRan (elabStmt1With C rc (.ret (some e))) sc st P st' →
      stmtQ C (.ret (some e)) sc st P st' :=
  (jump_cases C kernel rc).2 (.ret (some e)) rfl

/-- The actual knot's statement arm refuses `continue;`. -/
example (kernel : elabKernelTotal) (C : Contract) :
    Refuses (elabStmtPWith C (elabRec C ()) .cont) :=
  jump_refuses C _ ⟨(kernel.1 C).1.2.2.2.2.1, (kernel.1 C).1.2.2.2.1⟩ .cont rfl

/-- A simulated body completes at a checked frame exactly when it completes
at an unchecked one. -/
example {b : Body} {u : Emitted} {m : Solidity.Lowering.V07.ContextMap b.ctx u.Γ}
    (sim : RunSim b u m) (G : Source.Glob b.E) (F : Source.Fr) (src : Source.EMState b.E b.ctx)
    (n : Nat)
    (done : (sourceRun b G { F with checked := true } n 0 none src).1 ≠ .error .timeout)
    (done' : (sourceRun b G { F with checked := false } n 0 none src).1 ≠ .error .timeout) :
    (∃ x, (sourceRun b G { F with checked := true } n 0 none src).1 = .ok x) ↔
      ∃ x, (sourceRun b G { F with checked := false } n 0 none src).1 = .ok x :=
  sim.frame_blind G G _ _ 0 0 none none src n done done'

/-- info: 'Solidity.Correctness.Lowering.Sim.jump_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms jump_cases

/-- info: 'Solidity.Correctness.Lowering.Sim.one_not_runSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms one_not_runSim

/-- info: 'Solidity.Correctness.Lowering.Sim.stmt_cases_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stmt_cases_of

end Solidity.Examples.Lowering.Sim.Stmt
