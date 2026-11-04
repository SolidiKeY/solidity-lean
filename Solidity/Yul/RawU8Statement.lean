import Solidity.Yul.LocalU8Statement
import Solidity.Yul.RawCoherent

/-! Checked uint8 expression statements over the existing raw LOCAL frame.
Preparation preserves the entire word view; capture retains every partial raw
word. Source agreement requires checked execution and exact input coherence.
No general Source adapter or dirty-value decoder is supplied. -/
namespace Solidity.Yul.RawU8Statement

def localRun {ctx : Solidity.Source.Ctx} {expr}
    (proof : LocalU8Expr.Supported ctx.env ctx.tys expr)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × LocalState ctx.env ctx.tys :=
  LocalU8Statement.run proof pipeline fuel (RawCoherent.prepare state)

def run {ctx : Solidity.Source.Ctx} {expr}
    (proof : LocalU8Expr.Supported ctx.env ctx.tys expr)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  let out := localRun proof pipeline fuel state
  (out.1,RawCoherent.capture state out.2)

theorem view {ctx : Solidity.Source.Ctx} {expr}
    (proof : LocalU8Expr.Supported ctx.env ctx.tys expr)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    RawFrame.view (run proof pipeline fuel state).2 =
      localWordCells ctx (localRun proof pipeline fuel state).2.1 := by rfl

theorem zero_view {ctx : Solidity.Source.Ctx} {expr}
    (proof : LocalU8Expr.Supported ctx.env ctx.tys expr)
    (pipeline : Solidity.Roadmap.Pipeline) (state : RawFrame.State ctx) :
    RawFrame.view (run proof pipeline 0 state).2 = RawFrame.view state := by
  simp only [run,localRun,LocalU8Statement.zero,RawCoherent.capture_view,RawCoherent.prepare_view]

theorem clean_next : ∀ (ctx : Solidity.Source.Ctx)
 (expr : Solidity.Source.RExpr ctx.env ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (proof : Solidity.Yul.LocalU8Expr.Supported ctx.env ctx.tys expr)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel : Nat) (locals : Solidity.Source.Locals ctx.env.layout ctx.tys)
 (world : Solidity.Source.St ctx.env),
 ∃ next : Solidity.Source.Locals ctx.env.layout ctx.tys × Solidity.Source.St ctx.env,
 (Solidity.Yul.LocalU8Statement.run proof glob.pipeline fuel
   (Solidity.Yul.LocalState.ofClean (locals,world))).2 = Solidity.Yul.LocalState.ofClean next := by
  intro ctx expr proof glob frame checked fuel locals world
  cases fuel with
  | zero => exact ⟨(locals,world),rfl⟩
  | succ fuel =>
    rw [LocalU8Statement.step,LocalU8Expr.source_agrees proof glob frame checked fuel (locals,world)]
    exact ⟨((Solidity.Source.evalE glob frame fuel expr).run (locals,world)).2,rfl⟩

theorem correct : ∀ (ctx : Solidity.Source.Ctx)
 (expr : Solidity.Source.RExpr ctx.env ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (proof : Solidity.Yul.LocalU8Expr.Supported ctx.env ctx.tys expr)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawU8Statement.run proof glob.pipeline fuel state).2 = true ∧
 Solidity.Yul.RawCoherent.observe (Solidity.Yul.RawU8Statement.run proof glob.pipeline fuel state) =
 some ((Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.expr (R:=returns) (M:=modifier) (k:=control) expr) state.clean).run
     (Solidity.Source.L0 ctx.env,state.world)) := by
  intro ctx expr proof glob frame checked fuel nps ph returns modifier control state same
  obtain ⟨next, clean⟩ := clean_next ctx expr proof glob frame checked fuel state.clean state.world
  have agreement := LocalU8Statement.source_agrees ctx.env ctx.tys expr proof glob frame checked
    fuel nps ph returns modifier control state.clean state.world
  unfold run localRun
  rw [RawCoherent.prepare_coherent state same]
  generalize actual : LocalU8Statement.run proof glob.pipeline fuel
    (LocalState.ofClean (state.clean,state.world)) = out at clean agreement ⊢
  rcases out with ⟨tag,final⟩
  dsimp only at clean
  rw [clean] at agreement ⊢
  exact ⟨RawCoherent.capture_coherent state next.1 next.2,
    (RawCoherent.observe_capture state tag next.1 next.2).trans agreement⟩


theorem localRun_coherent {ctx : Solidity.Source.Ctx} {expr}
    (proof : LocalU8Expr.Supported ctx.env ctx.tys expr)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx)
    (same : RawCoherent.coherent state = true) :
    localRun proof pipeline fuel state =
      LocalU8Statement.run proof pipeline fuel (LocalState.ofClean (state.clean,state.world)) := by
  simp only [localRun,RawCoherent.prepare_coherent state same]

end Solidity.Yul.RawU8Statement
