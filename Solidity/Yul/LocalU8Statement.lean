import Solidity.Yul.LocalU8Agreement
import Solidity.Yul.LocalExprStatement

/-! Checked uint8 Source expression statements over the intrinsic LOCAL extension.
This consumer keeps raw partial locals and the pipeline's operand order.
Source agreement requires the actual checked frame and genuinely clean input;
this is not Yul arithmetic or an implicit dirty-local readback policy. -/
namespace Solidity.Yul.LocalU8Statement

def run {env ctx expr} (proof : LocalU8Expr.Supported env ctx expr)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : LocalState env ctx) :
    Solidity.Source.R Unit × LocalState env ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | fuel+1 =>
      let out := LocalU8Expr.eval proof pipeline fuel state
      (out.1.map (fun _ => ()),out.2)

theorem zero {env ctx expr} (proof : LocalU8Expr.Supported env ctx expr)
    (pipeline : Solidity.Roadmap.Pipeline) (state : LocalState env ctx) :
    run proof pipeline 0 state = (.error .timeout,state) := by rfl

theorem step {env ctx expr} (proof : LocalU8Expr.Supported env ctx expr)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : LocalState env ctx) :
    run proof pipeline (fuel+1) state =
      (let out := LocalU8Expr.eval proof pipeline fuel state
       (out.1.map (fun _ => ()),out.2)) := by rfl

/-- Concrete checked-frame Source statement equality for every certified tree and horizon. -/
theorem source_agrees : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env ctx Solidity.Yul.LocalU8Expr.Ty)
 (proof : Solidity.Yul.LocalU8Expr.Supported env ctx expr)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr),
 frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (locals : Solidity.Source.Locals env.layout ctx) (world : Solidity.Source.St env),
 Solidity.Yul.LocalExprStatement.project
   (Solidity.Yul.LocalU8Statement.run proof glob.pipeline fuel
     (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.expr (R := returns) (M := modifier) (k := control) expr) locals).run
     (Solidity.Source.L0 env,world)) := by
  intro env ctx expr proof glob frame checked fuel nps ph returns modifier control locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have agrees := LocalU8Expr.source_agrees proof glob frame checked fuel (locals,world)
    cases actual : (Solidity.Source.evalE glob frame fuel expr).run (locals,world) with
    | mk result next =>
      rcases next with ⟨nextLocals,nextWorld⟩
      let next := (nextLocals,nextWorld)
      rw [actual] at agrees
      cases result with
      | error halt =>
        change LocalU8Expr.eval proof glob.pipeline fuel (LocalState.ofClean (locals,world)) =
          (.error halt,LocalState.ofClean next) at agrees
        rw [step,agrees]
        have sub : (Solidity.Source.EM.sub (Γ := []) locals
            (Solidity.Source.evalE glob frame fuel expr)).run (Solidity.Source.L0 env,world) =
              (.error halt,(Solidity.Source.L0 env,next.2)) := by
          have actualRun : Solidity.Source.evalE (plan := none) glob frame fuel expr (locals,world) =
            (.error halt,(nextLocals,nextWorld)) := actual
          simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
          rfl
        rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub]
        rfl
      | ok value =>
        cases value with
        | val value =>
          cases value with
          | int value valid =>
            change LocalU8Expr.eval proof glob.pipeline fuel (LocalState.ofClean (locals,world)) =
              (.ok (.clean (.int value valid)),LocalState.ofClean next) at agrees
            rw [step,agrees]
            have sub : (Solidity.Source.EM.sub (Γ := []) locals
                (Solidity.Source.evalE glob frame fuel expr)).run (Solidity.Source.L0 env,world) =
                  (.ok (.val (.int value valid),next.1),(Solidity.Source.L0 env,next.2)) := by
              have actualRun : Solidity.Source.evalE (plan := none) glob frame fuel expr (locals,world) =
                (.ok (.val (.int value valid)),(nextLocals,nextWorld)) := actual
              simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
              rfl
            rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub]
            simp only [Except.map,LocalExprStatement.project,LocalState.ofClean,LocalValues.clean_ofClean]
            rfl
          | memRef impossible _ => cases impossible
          | storRef impossible _ => cases impossible
          | cdRef impossible _ => cases impossible

end Solidity.Yul.LocalU8Statement
