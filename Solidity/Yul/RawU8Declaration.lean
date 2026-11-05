import Solidity.Yul.RawPreparedInteger
import Solidity.Yul.RawU8Statement

/-! Checked uint8 expression declarations preserve actual partial raw locals.
The zero-valued backup is metadata for an incoherent result, not cleanup.
Source agreement requires genuine checked/coherent input. -/
namespace Solidity.Yul.RawU8Declaration
def run {ctx expr} (name : String)
    (proof : LocalU8Expr.Supported ctx.env ctx.tys expr)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Sum (Solidity.Source.Halt × RawFrame.State ctx)
      (RawFrame.State (ctx.push name LocalU8Expr.Ty)) :=
  match fuel with
  | 0 => .inl (.timeout,state)
  | n+1 =>
    let actual := LocalU8Expr.eval proof pipeline n (RawCoherent.prepare state)
    match actual.1 with
    | .error halt => .inl (halt,RawCoherent.capture state actual.2)
    | .ok value =>
      .inr (RawCoherent.capture
        (RawFrame.ofClean (.cons (.int 0 (by decide)) state.clean) state.world)
        ((value,actual.2.1),actual.2.2))
end Solidity.Yul.RawU8Declaration

namespace Solidity.Yul.RawU8Declaration
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (expr : Solidity.Source.RExpr ctx.env ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (proof : Solidity.Yul.LocalU8Expr.Supported ctx.env ctx.tys expr)
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 (match Solidity.Yul.RawU8Declaration.run name proof glob.pipeline fuel state with
 | .inl failure => Solidity.Yul.RawCoherent.coherent failure.2 = true
 | .inr next => Solidity.Yul.RawCoherent.coherent next = true) ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
     (k := control) (Γ := ctx.tys) (τ := Solidity.Yul.LocalU8Expr.Ty) expr (by rfl)) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawPreparedInteger.project
   (Solidity.Yul.RawU8Declaration.run name proof glob.pipeline fuel state) := by
  intro ctx name expr proof returns modifier control glob frame checked fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have agrees := LocalU8Expr.source_agrees proof glob frame checked fuel (state.clean,state.world)
    cases actual : (Solidity.Source.evalE glob frame fuel expr).run (state.clean,state.world) with
    | mk tag next =>
      rcases next with ⟨locals,world⟩
      rw [actual] at agrees
      cases tag with
      | error halt =>
        change LocalU8Expr.eval proof glob.pipeline fuel (LocalState.ofClean (state.clean,state.world)) =
          (.error halt,LocalState.ofClean (locals,world)) at agrees
        have sub : (Solidity.Source.EM.sub (Γ := []) state.clean
          (do Solidity.Source.getV (← Solidity.Source.convRV frame fuel LocalU8Expr.Ty
            (← Solidity.Source.evalE glob frame fuel expr)))).run (Solidity.Source.L0 ctx.env,state.world) =
            (.error halt,(Solidity.Source.L0 ctx.env,world)) := by
          have converted : (do Solidity.Source.getV (← Solidity.Source.convRV frame fuel LocalU8Expr.Ty
              (← Solidity.Source.evalE glob frame fuel expr))).run (state.clean,state.world) =
              (.error halt,(locals,world)) := by
            rw [Solidity.Source.Hoare.run_bind,actual]
          have actualRun : (do Solidity.Source.getV (← Solidity.Source.convRV frame fuel LocalU8Expr.Ty
              (← Solidity.Source.evalE glob frame fuel expr))) (state.clean,state.world) =
              (.error halt,(locals,world)) := converted
          simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
        simp only [run,RawCoherent.prepare_coherent state same,agrees]
        constructor
        · exact RawCoherent.capture_coherent state locals world
        · rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub]
          rw [RawCoherent.capture_ofClean]
          rfl
      | ok value =>
        cases value with
        | val value =>
          change LocalU8Expr.eval proof glob.pipeline fuel (LocalState.ofClean (state.clean,state.world)) =
            (.ok (.clean value),LocalState.ofClean (locals,world)) at agrees
          have sub : (Solidity.Source.EM.sub (Γ := []) state.clean
            (do Solidity.Source.getV (← Solidity.Source.convRV frame fuel LocalU8Expr.Ty
              (← Solidity.Source.evalE glob frame fuel expr)))).run (Solidity.Source.L0 ctx.env,state.world) =
              (.ok (value,locals),(Solidity.Source.L0 ctx.env,world)) := by
            have converted : (do Solidity.Source.getV (← Solidity.Source.convRV frame fuel LocalU8Expr.Ty
                (← Solidity.Source.evalE glob frame fuel expr))).run (state.clean,state.world) =
                (.ok value,(locals,world)) := by
              rw [Solidity.Source.Hoare.run_bind,actual]
              rfl
            have actualRun : (do Solidity.Source.getV (← Solidity.Source.convRV frame fuel LocalU8Expr.Ty
                (← Solidity.Source.evalE glob frame fuel expr))) (state.clean,state.world) =
                (.ok value,(locals,world)) := converted
            simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
          simp only [run,RawCoherent.prepare_coherent state same,agrees]
          constructor
          · exact RawCoherent.capture_coherent (ctx := ctx.push name LocalU8Expr.Ty) _ (.cons value locals) world
          · rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub]
            have captured := RawCoherent.capture_ofClean (ctx := ctx.push name LocalU8Expr.Ty)
              (RawFrame.ofClean (.cons (.int 0 (by decide)) state.clean) state.world)
              (.cons value locals) world
            change RawCoherent.capture (ctx := ctx.push name LocalU8Expr.Ty)
              (RawFrame.ofClean (.cons (.int 0 (by decide)) state.clean) state.world)
              ((.clean value,(LocalState.ofClean (locals,world)).1),
                (LocalState.ofClean (locals,world)).2) = _ at captured
            rw [captured]
            rfl
end Solidity.Yul.RawU8Declaration
