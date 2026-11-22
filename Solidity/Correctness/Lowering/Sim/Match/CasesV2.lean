import Solidity.Correctness.Lowering.Sim.Stmt.Framed

/-!
# Shared frame-aware lowering cases (H1208)

This interface advances `Solidity.Goals.loweringBySimulation` by collecting
case conclusions at a fixed callback record. It reuses `SiteSim₂` (hence
`RunSim₂`) and the landed statement-arm interface without changing v1.
`of_v1` transfers each applicable v1 clause with its existing kernel and
`RecSim` hypotheses. It does not replace `RecSim` by a weaker v2 premise.

The interface is conditional, not a proof of its fields. In particular,
the third conjunct of `ExprCases` requires
`ElabSat (captureQ C) (hoistStmtWith C rc)`. The five callbacks constrained by
v1 `RecSim` do not constrain `rc.hoistTop`, used by declaration capture;
`passRec_sim` and `passRec_ran` in `Sim/Expr/Strength.lean` exhibit this
missing dependency. Moreover `SiteSim₂` still ties an output to a whole
body: it provides no composition law for captures followed by a statement,
or for a declaration extending the context. Adding a frame premise does
not supply those laws. No recursive v2 closure, per-arm proof, producer
totalization, downstream migration or final simulation is asserted here.
Loops remain outside these cases, just as in v1 `StmtCases`.
-/
namespace Solidity.Correctness.Lowering.Sim.CasesV2

open Solidity.Goals (ElabRan ElabSat elabStmtsStep elabKernelTotal)

variable [FreshNames] (C : Contract)

/-- Captures, whether of an expression or statement, at their whole-body sites. -/
def captureQ {α : Type} (_ : α) (sc : ElabScope) (st : ECtx × Nat)
    (out : SProg C × α) (st' : ECtx × Nat) : Prop :=
  ∀ raw, SiteSim₂ C raw sc st out.1 st'

/-- A block at its frame-aware whole-body site. -/
def blockQ (ss : List RawStmt) (sc : ElabScope) (st : ECtx × Nat)
    (P : SProg C) (st' : ECtx × Nat) : Prop :=
  SiteSim₂ C ss sc st P st'

/-- Expression captures in a family, using the existing v1 family partition. -/
def ExprArm (rc : ElabRec C) (family : ExprFamily) : Prop :=
  ∀ e, exprFamily e = family →
    ∀ sc st out st', ElabRan (hoistWith C rc e) sc st out st' → captureQ C e sc st out st'

/-- Expression and arithmetic conclusions at a fixed record; no recursion claim. -/
def ExprCases (rc : ElabRec C) : Prop :=
  ExprArm C rc .operand ∧ ExprArm C rc .arith ∧
  ElabSat (captureQ C) (hoistStmtWith C rc) ∧ Stmt.V2.StmtArm C rc .arith

/-- Statement conclusions, preserving the v1 exclusion of loops. -/
def StmtCases (rc : ElabRec C) : Prop :=
  Stmt.V2.StmtArm C rc .assign ∧ Stmt.V2.StmtArm C rc .declLocal ∧
  Stmt.V2.StmtArm C rc .opAssign ∧ Stmt.V2.StmtArm C rc .incDec ∧
  Stmt.V2.StmtArm C rc .require ∧ Stmt.V2.StmtArm C rc .assert ∧
  Stmt.V2.StmtArm C rc .revert ∧ Stmt.V2.StmtArm C rc .ite ∧
  Stmt.V2.StmtArm C rc .block ∧ Stmt.V2.StmtArm C rc .jump ∧
  ElabSat (blockQ C) (elabStmtsStep C rc)

/-- State and call conclusions, including the unchanged call-return parameters. -/
def StateCases (rc : ElabRec C) : Prop :=
  Stmt.V2.StmtArm C rc .declStorage ∧ Stmt.V2.StmtArm C rc .call ∧
  Stmt.V2.StmtArm C rc .state ∧ ExprArm C rc .state ∧
  ∀ f args res resW targets ctor resNew selfFrame sc st out st',
    ElabRan (elabCallRetWith C rc f args res resW targets ctor resNew selfFrame) sc st out st' →
    ∀ raw, SiteSim₂ C raw sc st out.1 st'

/-- The shared interface collects the three families at one callback record. -/
structure Cases (rc : ElabRec C) : Prop where
  exprs : ExprCases C rc
  stmts : StmtCases C rc
  states : StateCases C rc

/-- A v1 expression arm transfers site by site through the landed bridge. -/
theorem ExprArm.of_v1 {rc : ElabRec C} {family : ExprFamily}
    (h : Sim.ExprArm C rc family) : ExprArm C rc family :=
  fun e family sc st out st' ran raw => (h e family sc st out st' ran raw).frame

/-- Transfer expression conclusions without changing the recursive premise. -/
theorem ExprCases.of_v1 (kernel : elabKernelTotal) (h : Sim.ExprCases)
    (rc : ElabRec C) (sim : RecSim C rc) : ExprCases C rc := by
  obtain ⟨operand, arith, captures, scopes⟩ := h kernel C rc sim
  exact ⟨ExprArm.of_v1 C operand, ExprArm.of_v1 C arith,
    (fun s sc st out st' ran raw => (captures s sc st out st' ran raw).frame),
    Stmt.V2.StmtArm.of_v1 C scopes⟩

/-- Transfer statement conclusions, including the sequence clause. -/
theorem StmtCases.of_v1 (kernel : elabKernelTotal) (h : Sim.StmtCases)
    (rc : ElabRec C) (sim : RecSim C rc) : StmtCases C rc := by
  obtain ⟨assign, declLocal, opAssign, incDec, require, assert, revert, ite, block, jump,
    sequence⟩ := h kernel C rc sim
  exact ⟨Stmt.V2.StmtArm.of_v1 C assign, Stmt.V2.StmtArm.of_v1 C declLocal,
    Stmt.V2.StmtArm.of_v1 C opAssign, Stmt.V2.StmtArm.of_v1 C incDec,
    Stmt.V2.StmtArm.of_v1 C require, Stmt.V2.StmtArm.of_v1 C assert,
    Stmt.V2.StmtArm.of_v1 C revert, Stmt.V2.StmtArm.of_v1 C ite,
    Stmt.V2.StmtArm.of_v1 C block, Stmt.V2.StmtArm.of_v1 C jump,
    fun ss sc st P st' ran => (sequence ss sc st P st' ran).frame⟩

/-- Transfer state conclusions and the call-return capture clause. -/
theorem StateCases.of_v1 (kernel : elabKernelTotal) (h : Sim.StateCases)
    (rc : ElabRec C) (sim : RecSim C rc) : StateCases C rc := by
  obtain ⟨storage, call, state, reach, returned⟩ := h kernel C rc sim
  exact ⟨Stmt.V2.StmtArm.of_v1 C storage, Stmt.V2.StmtArm.of_v1 C call,
    Stmt.V2.StmtArm.of_v1 C state, ExprArm.of_v1 C reach,
    fun f args res resW targets ctor resNew selfFrame sc st out st' ran raw =>
      (returned f args res resW targets ctor resNew selfFrame sc st out st' ran raw).frame⟩

/-- Applicable v1 hypotheses supply the shared frame-aware interface. -/
theorem of_v1 (kernel : elabKernelTotal) (exprs : Sim.ExprCases)
    (stmts : Sim.StmtCases) (states : Sim.StateCases) (rc : ElabRec C) (sim : RecSim C rc) :
    Cases C rc :=
  ⟨ExprCases.of_v1 C kernel exprs rc sim, StmtCases.of_v1 C kernel stmts rc sim,
    StateCases.of_v1 C kernel states rc sim⟩

end Solidity.Correctness.Lowering.Sim.CasesV2
