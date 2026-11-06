import Solidity.Yul.LocalExprStatement

/-! Context-growing Boolean declaration execution using the existing intrinsic
control-expression producer. Raw values and partial local effects are retained;
the optional Source projection never cleans raw constructors. -/
namespace Solidity.Yul.LocalBoolInitialization

inductive Result (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) where
  | normal : LocalState env (.bool :: types) → Result env types
  | halted : Solidity.Source.Halt → LocalState env types → Result env types

def finish {env types}
    (actual : Solidity.Source.R (LocalValue env .bool) × LocalState env types) : Result env types :=
  match actual.1 with
  | .error halt => .halted halt actual.2
  | .ok value => .normal ((value,actual.2.1),actual.2.2)

def run {env types expr} (proof : LocalBoolControl.Supported env types expr)
    (fuel : Nat) (state : LocalState env types) : Result env types :=
  match fuel with
  | 0 => .halted .timeout state
  | fuel+1 => finish (LocalBoolControl.eval proof fuel state)

def project {env types} (result : Result env types) :
    Option (Solidity.Source.R (Solidity.Source.Out env.layout types (.bool :: types)) ×
      (Solidity.Source.Locals env.layout [] × Solidity.Source.St env)) :=
  Result.casesOn (motive := fun _ => Option
    (Solidity.Source.R (Solidity.Source.Out env.layout types (.bool :: types)) ×
      (Solidity.Source.Locals env.layout [] × Solidity.Source.St env))) result
    (fun next => (LocalValues.clean? (.bool :: types) next.1).map
      (fun locals => (.ok (.normal locals),(Solidity.Source.L0 env,next.2))))
    (fun halt next => some (.error halt,(Solidity.Source.L0 env,next.2)))



theorem source_agrees : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env types .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported env types expr)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolInitialization.project
   (Solidity.Yul.LocalBoolInitialization.run proof fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.declInit (R := returns) (M := modifier) (k := control)
     (τ := .bool) expr (by rfl)) locals).run (Solidity.Source.L0 env,world)) := by
  intro env types expr proof glob frame fuel nps ph returns modifier control locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have agrees := Solidity.Yul.LocalBoolControl.source_agrees proof glob frame fuel (locals,world)
    cases actual : (Solidity.Source.evalE glob frame fuel expr).run (locals,world) with
    | mk result next =>
      rcases next with ⟨nextLocals,nextWorld⟩
      rw [actual] at agrees
      cases result with
      | error halt =>
        change Solidity.Yul.LocalBoolControl.eval proof fuel (Solidity.Yul.LocalState.ofClean (locals,world)) =
          (.error halt,Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld)) at agrees
        simp only [Solidity.Yul.LocalBoolInitialization.run,agrees,
          Solidity.Yul.LocalBoolInitialization.finish,Solidity.Yul.LocalBoolInitialization.project]
        have sub : (Solidity.Source.EM.sub (Γ := []) locals
          (do Solidity.Source.getV (← Solidity.Source.convRV frame fuel .bool
            (← Solidity.Source.evalE glob frame fuel expr)))).run (Solidity.Source.L0 env,world) =
          (.error halt,(Solidity.Source.L0 env,nextWorld)) := by
          have converted : (do Solidity.Source.getV (← Solidity.Source.convRV frame fuel .bool
              (← Solidity.Source.evalE glob frame fuel expr))).run (locals,world) =
              (.error halt,(nextLocals,nextWorld)) := by
            rw [Solidity.Source.Hoare.run_bind,actual]
          have actualRun : (do Solidity.Source.getV (← Solidity.Source.convRV frame fuel .bool
              (← Solidity.Source.evalE glob frame fuel expr))) (locals,world) =
              (.error halt,(nextLocals,nextWorld)) := converted
          simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
        rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub]
        rfl
      | ok value =>
        cases value with
        | val value =>
          cases value with
          | bool value =>
            change Solidity.Yul.LocalBoolControl.eval proof fuel (Solidity.Yul.LocalState.ofClean (locals,world)) =
              (.ok (.clean (.bool value)),Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld)) at agrees
            simp only [Solidity.Yul.LocalBoolInitialization.run,agrees,
              Solidity.Yul.LocalBoolInitialization.finish,Solidity.Yul.LocalBoolInitialization.project]
            have sub : (Solidity.Source.EM.sub (Γ := []) locals
              (do Solidity.Source.getV (← Solidity.Source.convRV frame fuel .bool
                (← Solidity.Source.evalE glob frame fuel expr)))).run (Solidity.Source.L0 env,world) =
              (.ok (.bool value,nextLocals),(Solidity.Source.L0 env,nextWorld)) := by
              have converted : (do Solidity.Source.getV (← Solidity.Source.convRV frame fuel .bool
                  (← Solidity.Source.evalE glob frame fuel expr))).run (locals,world) =
                  (.ok (.bool value),(nextLocals,nextWorld)) := by
                rw [Solidity.Source.Hoare.run_bind,actual]
                rfl
              have actualRun : (do Solidity.Source.getV (← Solidity.Source.convRV frame fuel .bool
                  (← Solidity.Source.evalE glob frame fuel expr))) (locals,world) =
                  (.ok (.bool value),(nextLocals,nextWorld)) := converted
              simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
            rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub]
            change (Solidity.Yul.LocalValues.clean? (.bool :: types)
              (Solidity.Yul.LocalValues.ofClean (Solidity.Source.Locals.cons (.bool value) nextLocals))).map
              (fun finalLocals =>
                ((Except.ok (Solidity.Source.Out.normal finalLocals) :
                  Solidity.Source.R (Solidity.Source.Out env.layout types (.bool :: types))),
                  (Solidity.Source.L0 env,nextWorld))) =
              some (.ok (.normal (Solidity.Source.Locals.cons (.bool value) nextLocals)),
                (Solidity.Source.L0 env,nextWorld))
            rw [Solidity.Yul.LocalValues.clean_ofClean]
            rfl
          | memRef impossible _ => cases impossible
          | storRef impossible _ => cases impossible
          | cdRef impossible _ => cases impossible


end Solidity.Yul.LocalBoolInitialization
