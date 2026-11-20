import Solidity.Correctness.Lowering.Sim.Match.CasesV2

/-! # The shared frame-aware interface, used under its exact v1 hypotheses -/
namespace Solidity.Examples.Lowering.Sim.CasesV2

open Solidity.Goals (elabKernelTotal ElabRan)
open Solidity.Correctness.Lowering.Sim

variable [FreshNames]

/-- All three v1 case families transfer at a record satisfying v1 `RecSim`. -/
example (C : Contract) (kernel : elabKernelTotal) (exprs : ExprCases)
    (stmts : StmtCases) (states : StateCases) (rc : ElabRec C) (sim : RecSim C rc) :
    CasesV2.Cases C rc :=
  CasesV2.of_v1 C kernel exprs stmts states rc sim

/-- A successful block run projects to the existing frame-aware site relation. -/
example (C : Contract) (kernel : elabKernelTotal) (stmts : StmtCases)
    (rc : ElabRec C) (sim : RecSim C rc) (ss : List RawStmt) (sc : ElabScope)
    (st st' : ECtx × Nat) (P : SProg C)
    (ran : ElabRan (Solidity.Goals.elabStmtsStep C rc ss) sc st P st') :
    SiteSim₂ C ss sc st P st' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, sequence⟩ :=
    CasesV2.StmtCases.of_v1 C kernel stmts rc sim
  exact sequence ss sc st P st' ran

/-- The unchanged run bridge retains both simulation directions and stability. -/
example (b : Solidity.Goals.Shrink.Lowering.Body)
    (u : Solidity.Goals.Shrink.Lowering.Emitted)
    (m : Solidity.Lowering.V07.ContextMap b.ctx u.Γ) (h : RunSim b u m) : RunSim₂ b u m :=
  h.frame

end Solidity.Examples.Lowering.Sim.CasesV2
