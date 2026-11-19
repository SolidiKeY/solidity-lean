import Solidity.Correctness.Lowering.Sim.Expr.Capture
import Solidity.Correctness.Lowering.Sim.Expr.Strength

/-!
# The run obligation under the frame relation, v2 (ls2-expressions, H1205)

`RunSim` (v1, `Sim/Match/Cases.lean`, frozen) ranges over every Source frame,
and `globRel` has no frame: at a body that writes storage a static frame
reverts in Source and completes in the model, so v1 is not provable there.
This is the additive v2 of the obligations this lane's cases conclude, next to
v1 and with a bridge from it:

* `RunSim₂`: `RunSim` with its three run clauses under
  `frameRel G F tgt` (`Sim/Match/Relations.lean`): the Source frame is the
  model's transaction, not static, checked. `LowerFresh` and total initial
  matching are unchanged.
* `SiteSim₂`: `SiteSim` with `RunSim₂`.
* Bridges: `RunSim.frame`, `SiteSim.frame` (v1 gives v2), and
  `sites₂_of_exprCases` (the v1 expression cases give every v2 site).
* `hoistStmt_pushIncDec_sat₂`: the case at `b.push()++` at v2, from the v2
  obligation of `rc.hoist`.

## Limitations

* Only the obligations are restated. A v2 of `ExprCases` is not: with the
  record constrained on five fields and whole-body sites it would again imply
  every site (`Sim/Expr/Strength.lean`); it needs the shared statement-level
  interface.
* That the forward clause holds under `frameRel` is not proved here.
* `Diagram.Simulates` (`Goals/LoweringDiagram.lean`) has no v2 here: a goal
  statement belongs to its owner.
-/
namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals (ElabRan elabKernelTotal)
open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)
open Solidity.Correctness.Lowering.Checker (Output)

variable [FreshNames]

/-- **The per-run obligations, v2**: those of `RunSim`, the run clauses at
Source frames related to the model state by `frameRel`. -/
def RunSim₂ (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ) : Prop :=
  LowerFresh b u ∧
  (∀ src : Source.EMState b.E b.ctx, ∃ tgt : State u.C u.Γ,
    m.Related (fun τ v => diagram.valRel τ v) src.1 tgt.env ∧ diagram.globRel src.2 tgt) ∧
  ∃ emb : Thin u.Γ u.output.program.1,
  ∀ (G : Source.Glob b.E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph b.E))
    (src : Source.EMState b.E b.ctx) (tgt : State u.C u.Γ),
    m.Related (fun τ v => diagram.valRel τ v) src.1 tgt.env → diagram.globRel src.2 tgt →
    frameRel G F tgt →
    (∀ n, (sourceRun b G F n nps ph src).1 ≠ .error .timeout →
      diagram.Final m emb (sourceRun b G F n nps ph src)
        (u.output.program.2.runF (diagram.fuel n) tgt)) ∧
    (∀ n n', n ≤ n' → (sourceRun b G F n nps ph src).1 ≠ .error .timeout →
      sourceRun b G F n' nps ph src = sourceRun b G F n nps ph src) ∧
    (∀ n, u.output.program.2.runF n tgt ≠ .error .diverge →
      ∃ j, diagram.Final m emb (sourceRun b G F j nps ph src) (u.output.program.2.runF n tgt))

omit [FreshNames] in
/-- **Bridge**: the v1 obligations give the v2 ones. -/
theorem RunSim.frame {b : Body} {u : Emitted} {m : ContextMap b.ctx u.Γ} (h : RunSim b u m) :
    RunSim₂ b u m :=
  ⟨h.1, h.2.1, h.2.2.choose, fun G F nps ph src tgt related glob _ =>
    h.2.2.choose_spec G F nps ph src tgt related glob⟩

variable (C : Contract)

/-- **The obligations at a site, v2**: `SiteSim` with `RunSim₂`. -/
def SiteSim₂ (raw : List RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C)
    (st' : ECtx × Nat) : Prop :=
  ∀ (b : Body) (Γ : Ctx) (o : Output C Γ) (m : ContextMap b.ctx Γ),
    Elaborated C o raw sc st P st' → Lowered b ⟨C, Γ, o⟩ → Threaded b ⟨C, Γ, o⟩ →
    Accepted ⟨C, Γ, o⟩ → diagram.Assoc b ⟨C, Γ, o⟩ m → RunSim₂ b ⟨C, Γ, o⟩ m

/-- **Bridge**: a v1 site gives the v2 site. -/
theorem SiteSim.frame {raw : List RawStmt} {sc : ElabScope} {st st' : ECtx × Nat} {P : SProg C}
    (h : SiteSim C raw sc st P st') : SiteSim₂ C raw sc st P st' :=
  fun b Γ o m run lowered threaded accepted assoc =>
    (h b Γ o m run lowered threaded accepted assoc).frame

/-- **Bridge**: the v1 expression cases give every v2 site. -/
theorem sites₂_of_exprCases (kernel : elabKernelTotal) (exprs : ExprCases) (raw : List RawStmt)
    (sc : ElabScope) (st : ECtx × Nat) (P : SProg C) (st' : ECtx × Nat) :
    SiteSim₂ C raw sc st P st' :=
  (sites_of_exprCases kernel exprs C raw sc st P st').frame

/-- **The case at `b.push()++`, v2**: its captures are those of `rc.hoist`,
whose v2 obligation is the hypothesis. -/
theorem hoistStmt_pushIncDec_sat₂ (rc : ElabRec C)
    (hoist : ∀ e sc st out st', ElabRan (rc.hoist e) sc st out st' →
      ∀ raw, SiteSim₂ C raw sc st out.1 st')
    (op : IncDec) (b : RawExpr) (sc : ElabScope) (st : ECtx × Nat) (out : SProg C × RawStmt)
    (st' : ECtx × Nat) (ran : ElabRan (hoistStmtWith C rc (.pushIncDec op b)) sc st out st')
    (raw : List RawStmt) : SiteSim₂ C raw sc st out.1 st' := by
  rw [hoistStmt_pushIncDec] at ran
  obtain ⟨a, ran⟩ := ran_map C _ _ ran
  exact hoist b sc st _ st' ran raw

end Solidity.Correctness.Lowering.Sim
