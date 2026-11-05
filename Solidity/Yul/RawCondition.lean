import Solidity.Yul.RawSequence

/-! Actual certified Source boolean condition evaluation over the raw frame.
All words and partial state are retained. Clean Source agreement requires the
existing exact whole-word coherence premise, not an assumed child law. -/
namespace Solidity.Yul.RawCondition

def eval {ctx expr} (proof : LocalBoolControl.Supported ctx.env ctx.tys expr)
    (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Bool × RawFrame.State ctx :=
  let result := LocalBoolControl.eval proof fuel (RawCoherent.prepare state)
  (result.1.map LocalBoolControl.truth, RawCoherent.capture state result.2)

theorem source_eval {ctx expr} (proof : LocalBoolControl.Supported ctx.env ctx.tys expr)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel : Nat) (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    eval proof fuel state =
      (let source := (Solidity.Source.evalE glob frame fuel expr).run (state.clean,state.world)
       ((LocalBoolExpr.cleanOutcome source).1.map LocalBoolControl.truth,
        RawCoherent.capture state (LocalState.ofClean source.2))) := by
  unfold eval
  rw [RawCoherent.prepare_coherent state same,
    LocalBoolControl.source_agrees proof glob frame fuel (state.clean,state.world)]
  rfl

theorem invariant {ctx expr} (proof : LocalBoolControl.Supported ctx.env ctx.tys expr)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel : Nat) (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.coherent (eval proof fuel state).2 = true := by
  rw [source_eval proof glob frame fuel state same]
  exact RawCoherent.capture_coherent state _ _

theorem full_state {ctx expr} (proof : LocalBoolControl.Supported ctx.env ctx.tys expr)
    (fuel : Nat) (state : RawFrame.State ctx) :
    RawFrame.view (eval proof fuel state).2 =
        localWordCells ctx (LocalBoolControl.eval proof fuel (RawCoherent.prepare state)).2.1 ∧
      (eval proof fuel state).2.world =
        (LocalBoolControl.eval proof fuel (RawCoherent.prepare state)).2.2 :=
  ⟨rfl,rfl⟩

theorem sub_error {ctx : Solidity.Source.Ctx}
    (expr : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (locals next : Solidity.Source.Locals ctx.env.layout ctx.tys)
    (world nextWorld : Solidity.Source.St ctx.env) (halt : Solidity.Source.Halt)
    (actual : (Solidity.Source.evalE glob frame fuel expr).run (locals,world) =
      (.error halt,(next,nextWorld))) :
    (Solidity.Source.EM.sub (Γ := []) locals (Solidity.Source.evalE glob frame fuel expr)).run
      (Solidity.Source.L0 ctx.env,world) =
        (.error halt,(Solidity.Source.L0 ctx.env,nextWorld)) := by
  have actualRun : Solidity.Source.evalE glob frame fuel expr (locals,world) =
      (.error halt,(next,nextWorld)) := actual
  simp only [Solidity.Source.EM.sub, ExceptT.run, ExceptT.mk, actualRun]

theorem sub_bool {ctx : Solidity.Source.Ctx}
    (expr : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (locals next : Solidity.Source.Locals ctx.env.layout ctx.tys)
    (world nextWorld : Solidity.Source.St ctx.env) (value : Bool)
    (actual : (Solidity.Source.evalE glob frame fuel expr).run (locals,world) =
      (.ok (.val (.bool value)),(next,nextWorld))) :
    (Solidity.Source.EM.sub (Γ := []) locals (Solidity.Source.evalE glob frame fuel expr)).run
      (Solidity.Source.L0 ctx.env,world) =
        (.ok (.val (.bool value),next),(Solidity.Source.L0 ctx.env,nextWorld)) := by
  have actualRun : Solidity.Source.evalE glob frame fuel expr (locals,world) =
      (.ok (.val (.bool value)),(next,nextWorld)) := actual
  simp only [Solidity.Source.EM.sub, ExceptT.run, ExceptT.mk, actualRun]

end Solidity.Yul.RawCondition
