import Solidity.Yul.RawU8Horizon
import Solidity.Yul.Checks.RawU8Statement
/-! Completed whole-frame stability and actual checked Source transport.
Counterexamples retain changing timeout and cross-pipeline partial words;
no conclusion about the later timeout-example tag is required. -/
namespace Solidity.Yul.Checks.RawU8Horizon
namespace Old
export Solidity.Yul.Checks.RawU8Statement (ctx initial xCell)
export Solidity.Yul.Checks.RawU8Statement.Old (env order orderExpr assign sum readX timeout)
export Solidity.Yul.Checks.LocalU8Representation (assignExpr)
end Old
def witness : Nonempty (LocalU8Expr.Supported Old.ctx.env Old.ctx.tys Old.orderExpr) := ⟨Old.order⟩
theorem readStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Horizon.Old.env) (extra : Nat), Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Horizon.Old.readX pipeline (2+extra) (Solidity.Yul.Checks.RawU8Horizon.Old.initial 257 2 1 world) = Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Horizon.Old.readX pipeline 2 (Solidity.Yul.Checks.RawU8Horizon.Old.initial 257 2 1 world) := by
  intro pipeline world extra
  apply Solidity.Yul.RawU8Horizon.extension
  intro bad
  cases bad

theorem copyStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Horizon.Old.env) (extra : Nat), Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Horizon.Old.assign pipeline (3+extra) (Solidity.Yul.Checks.RawU8Horizon.Old.initial 2 257 2 world) = Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Horizon.Old.assign pipeline 3 (Solidity.Yul.Checks.RawU8Horizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  apply Solidity.Yul.RawU8Horizon.extension
  rw [(Solidity.Yul.Checks.RawU8Statement.rawCopy pipeline world).1]
  intro bad
  cases bad

theorem panicStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Horizon.Old.env) (extra : Nat), Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Horizon.Old.sum pipeline (4+extra) (Solidity.Yul.Checks.RawU8Horizon.Old.initial 511 1 2 world) = Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Horizon.Old.sum pipeline 4 (Solidity.Yul.Checks.RawU8Horizon.Old.initial 511 1 2 world) := by
  intro pipeline world extra
  apply Solidity.Yul.RawU8Horizon.extension
  rw [(Solidity.Yul.Checks.RawU8Statement.panicPrefix pipeline world).1]
  intro bad
  cases bad

theorem timeoutCounterexample : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Horizon.Old.env), Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Horizon.Old.timeout .legacy 5 (Solidity.Yul.Checks.RawU8Horizon.Old.initial 257 2 1 world) ≠ Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Horizon.Old.timeout .legacy 6 (Solidity.Yul.Checks.RawU8Horizon.Old.initial 257 2 1 world) := by
  intro world bad
  have later : (RawFrame.view (RawU8Statement.run Old.timeout .legacy 6 (Old.initial 257 2 1 world)).2 Old.xCell).val = 2 := by rfl
  have cells := congrArg (fun out : Solidity.Source.R Unit × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.xCell).val) bad
  dsimp only at cells
  rw [(Solidity.Yul.Checks.RawU8Statement.legacyPartial world).2.1,later] at cells
  cases cells

theorem zeroCounterexample : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Horizon.Old.env), Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Horizon.Old.readX pipeline 0 (Solidity.Yul.Checks.RawU8Horizon.Old.initial 257 2 1 world) ≠ Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Horizon.Old.readX pipeline 2 (Solidity.Yul.Checks.RawU8Horizon.Old.initial 257 2 1 world) := by
  intro pipeline world bad
  have tags := congrArg Prod.fst bad
  cases tags

theorem pipelineCounterexample : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Horizon.Old.env), Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Horizon.Old.timeout .legacy 5 (Solidity.Yul.Checks.RawU8Horizon.Old.initial 257 2 1 world) ≠ Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Horizon.Old.timeout .viaIR 5 (Solidity.Yul.Checks.RawU8Horizon.Old.initial 257 2 1 world) := by
  intro world bad
  have cells := congrArg (fun out : Solidity.Source.R Unit × Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawU8Horizon.Old.ctx =>
    (Solidity.Yul.RawFrame.view out.2 Solidity.Yul.Checks.RawU8Horizon.Old.xCell).val) bad
  dsimp only at cells
  rw [(Solidity.Yul.Checks.RawU8Statement.legacyPartial world).2.1,
    (Solidity.Yul.Checks.RawU8Statement.viaIRPartial world).2.1] at cells
  cases cells

theorem sourceStable : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawU8Horizon.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (extra nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawU8Horizon.Old.ctx.env))
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawU8Horizon.Old.ctx.env.layout Solidity.Yul.Checks.RawU8Horizon.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Horizon.Old.ctx.env),
 (Solidity.Source.execS glob frame (3+extra) nps ph
   (Solidity.Source.RStmt.expr (R:=returns) (M:=modifier) (k:=control) Solidity.Yul.Checks.RawU8Horizon.Old.assignExpr) locals).run
     (Solidity.Source.L0 Solidity.Yul.Checks.RawU8Horizon.Old.ctx.env,world) =
 (Solidity.Source.execS glob frame 3 nps ph
   (Solidity.Source.RStmt.expr (R:=returns) (M:=modifier) (k:=control) Solidity.Yul.Checks.RawU8Horizon.Old.assignExpr) locals).run
     (Solidity.Source.L0 Solidity.Yul.Checks.RawU8Horizon.Old.ctx.env,world) := by
  intro glob frame checked extra nps ph returns modifier control locals world
  have coherent := Solidity.Yul.RawCoherent.coherent_ofClean (ctx := Solidity.Yul.Checks.RawU8Horizon.Old.ctx) locals world
  have ready : (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Horizon.Old.assign glob.pipeline 3 (Solidity.Yul.RawFrame.ofClean locals world)).1 ≠ .error .timeout := by
    change (Solidity.Yul.RawU8Statement.localRun Solidity.Yul.Checks.RawU8Horizon.Old.assign glob.pipeline 3 (Solidity.Yul.RawFrame.ofClean locals world)).1 ≠ _
    rw [Solidity.Yul.RawU8Statement.localRun_coherent Solidity.Yul.Checks.RawU8Horizon.Old.assign glob.pipeline 3 (Solidity.Yul.RawFrame.ofClean locals world) coherent]
    intro bad
    cases bad
  exact Solidity.Yul.RawU8Horizon.sourceExtension Solidity.Yul.Checks.RawU8Horizon.Old.ctx Solidity.Yul.Checks.RawU8Horizon.Old.assignExpr Solidity.Yul.Checks.RawU8Horizon.Old.assign glob frame checked
    3 extra nps ph returns modifier control (Solidity.Yul.RawFrame.ofClean locals world) coherent ready

theorem dirtyRefusal : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Horizon.Old.env), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawU8Horizon.Old.initial 2 257 2 world) = false := by
  exact Solidity.Yul.Checks.RawU8Statement.dirtyRefusal

#print axioms Solidity.Yul.RawU8Horizon.localExtension
#print axioms Solidity.Yul.RawU8Horizon.extension
#print axioms Solidity.Yul.RawU8Horizon.successor
#print axioms Solidity.Yul.RawU8Horizon.sourceExtension
#print axioms readStable
#print axioms copyStable
#print axioms panicStable
#print axioms timeoutCounterexample
#print axioms zeroCounterexample
#print axioms pipelineCounterexample
#print axioms sourceStable
#print axioms dirtyRefusal
end Solidity.Yul.Checks.RawU8Horizon
