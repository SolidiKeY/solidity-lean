import Solidity.Yul.RawLoopFailure
import Solidity.Source.Semantics

/-! Actual Source iteration timeouts and firstDone horizons for concrete no-break
Boolean body certificates. Coherence is required for raw inputs and discharged
only via ofClean for clean locals. Actual reached worlds are retained; no
arbitrary initialized-loop or dirty Source adequacy claim. -/
namespace Solidity.Yul.RawSourceLoopTimeout


theorem post_timeout : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx)
 (_same : Solidity.Yul.RawCoherent.coherent state = true),
 (Solidity.Source.forIter glob frame fuel nps ph .none (.some post) stmt state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) =
 (.error .timeout,(Solidity.Source.L0 ctx.env,(Solidity.Yul.RawSourceForPost.run (.base (.literal true)) step (Solidity.Yul.RawSourceAdapter.body body) fuel state).2.world)) := by
  intro ctx returns modifier u stmt body safe post step glob frame fuel nps ph state same
  rw [Solidity.Yul.RawSourceForPost.Absent.source_true]
  have agreement := (Solidity.Yul.RawSourceForPost.correct (.base (.literal true)) step
    (Solidity.Yul.RawSourceAdapter.body body) glob frame fuel nps ph state same).2
  have timed := Solidity.Yul.RawLoopFailure.post_timeout ctx returns modifier u stmt body safe post step fuel state
  simpa only [Solidity.Yul.RawSequence.represented,timed,Except.map] using agreement

theorem no_post_timeout : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx)
 (_same : Solidity.Yul.RawCoherent.coherent state = true),
 (Solidity.Source.forIter glob frame fuel nps ph .none .none stmt state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) =
 (.error .timeout,(Solidity.Source.L0 ctx.env,(Solidity.Yul.RawSourceAdapterLoop.run (.base (.literal true)) (Solidity.Yul.RawSourceAdapter.body body) fuel state).2.world)) := by
  intro ctx returns modifier u stmt body safe glob frame fuel nps ph state same
  rw [Solidity.Yul.RawSourceForPost.Absent.source_true]
  have agreement := (Solidity.Yul.RawSourceForIter.correct (.base (.literal true))
    (Solidity.Yul.RawSourceAdapter.body body) glob frame fuel nps ph state same).2
  have timed : (Solidity.Yul.RawSourceAdapterLoop.run (.base (.literal true))
      (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 = .error .timeout := by
    rw [Solidity.Yul.RawAdapterLoopHorizon.body_agrees]
    exact Solidity.Yul.RawLoopFailure.no_post_timeout ctx returns modifier u stmt body safe fuel state
  simpa only [Solidity.Yul.RawSequence.represented,timed,Except.map] using agreement

theorem post_firstDone : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (_step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) (world : Solidity.Source.St ctx.env),
 ∀ bound, Solidity.Source.firstDone (fun fuel =>
 (Solidity.Source.forIter glob frame fuel nps ph .none (.some post) stmt locals).run (Solidity.Source.L0 ctx.env,world)) bound = none := by
  intro ctx returns modifier u stmt body safe post step glob frame nps ph locals world
  apply (Solidity.Source.firstDone_none_iff _).2
  intro fuel
  have actual := post_timeout ctx returns modifier u stmt body safe post step glob frame fuel nps ph
    (Solidity.Yul.RawFrame.ofClean locals world) (Solidity.Yul.RawCoherent.coherent_ofClean locals world)
  dsimp only [Solidity.Yul.RawFrame.ofClean] at actual
  rw [actual]
  rfl

theorem no_post_firstDone : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) (world : Solidity.Source.St ctx.env),
 ∀ bound, Solidity.Source.firstDone (fun fuel =>
 (Solidity.Source.forIter glob frame fuel nps ph .none .none stmt locals).run (Solidity.Source.L0 ctx.env,world)) bound = none := by
  intro ctx returns modifier u stmt body safe glob frame nps ph locals world
  apply (Solidity.Source.firstDone_none_iff _).2
  intro fuel
  have actual := no_post_timeout ctx returns modifier u stmt body safe glob frame fuel nps ph
    (Solidity.Yul.RawFrame.ofClean locals world) (Solidity.Yul.RawCoherent.coherent_ofClean locals world)
  dsimp only [Solidity.Yul.RawFrame.ofClean] at actual
  rw [actual]
  rfl

end Solidity.Yul.RawSourceLoopTimeout
