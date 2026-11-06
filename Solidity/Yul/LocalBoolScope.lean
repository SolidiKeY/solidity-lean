import Solidity.Yul.LocalBoolInitialization
import Solidity.Yul.RawLocalScope

/-! Scope closure around actual Boolean expression initialization.
Only a successful temporary head is dropped; initializer effects remain. -/
namespace Solidity.Yul.LocalBoolScope

def close {env types} (result : LocalBoolInitialization.Result env types) :
    Solidity.Source.R Unit × LocalState env types :=
  LocalBoolInitialization.Result.casesOn (motive := fun _ =>
    Solidity.Source.R Unit × LocalState env types) result
    (fun next => (.ok (), (next.1.2,next.2)))
    (fun halt next => (.error halt,next))

def run {env types expr} (proof : LocalBoolControl.Supported env types expr)
    (fuel : Nat) (state : LocalState env types) :
    Solidity.Source.R Unit × LocalState env types :=
  match fuel with
  | 0 => (.error .timeout,state)
  | fuel+1 => match fuel with
    | 0 => (.error .timeout,state)
    | fuel+1 => close (LocalBoolInitialization.run proof fuel state)

def project {env types}
    (result : Solidity.Source.R Unit × LocalState env types) :
    Option (Solidity.Source.R (Solidity.Source.Out env.layout types types) ×
      (Solidity.Source.Locals env.layout [] × Solidity.Source.St env)) :=
  match result.1 with
  | .error halt => some (.error halt,(Solidity.Source.L0 env,result.2.2))
  | .ok _ => (LocalValues.clean? types result.2.1).map
      (fun locals => (.ok (.normal locals),(Solidity.Source.L0 env,result.2.2)))



theorem source_agrees : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env types .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported env types expr)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolScope.project
   (Solidity.Yul.LocalBoolScope.run proof fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.block (.stmt
     (Solidity.Source.RStmt.declInit (R := returns) (M := modifier) (k := control)
       (τ := .bool) expr (by rfl)) .nil)) locals).run (Solidity.Source.L0 env,world)) := by
  intro env types expr proof glob frame fuel nps ph returns modifier control locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
        have expression := Solidity.Yul.LocalBoolControl.source_agrees proof glob frame fuel (locals,world)
        have declaration := Solidity.Yul.LocalBoolInitialization.source_agrees env types expr proof
          glob frame (fuel+1) nps ph returns modifier control locals world
        cases actual : (Solidity.Source.evalE glob frame fuel expr).run (locals,world) with
        | mk result next =>
          rcases next with ⟨nextLocals,nextWorld⟩
          rw [actual] at expression
          cases result with
          | error halt =>
            change Solidity.Yul.LocalBoolControl.eval proof fuel (Solidity.Yul.LocalState.ofClean (locals,world)) =
              (.error halt,Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld)) at expression
            rw [Solidity.Yul.LocalBoolInitialization.run,expression] at declaration
            change some ((Except.error halt : Solidity.Source.R
              (Solidity.Source.Out env.layout types (.bool :: types))),
              (Solidity.Source.L0 env,nextWorld)) = some _ at declaration
            have child := (Option.some.inj declaration).symm
            have items : (Solidity.Source.execItems glob frame (fuel+2) nps ph
              (.stmt (Solidity.Source.RStmt.declInit (R := returns) (M := modifier) (k := control)
                (τ := .bool) expr (by rfl)) .nil) locals).run (Solidity.Source.L0 env,world) =
              (.error halt,(Solidity.Source.L0 env,nextWorld)) := by
              rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,child]
            simp only [Solidity.Yul.LocalBoolScope.run,Solidity.Yul.LocalBoolInitialization.run,expression,
              Solidity.Yul.LocalBoolInitialization.finish,Solidity.Yul.LocalBoolScope.close,Solidity.Yul.LocalBoolScope.project]
            rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,items]
            rfl
          | ok value =>
            cases value with
            | val value =>
              cases value with
              | bool value =>
                change Solidity.Yul.LocalBoolControl.eval proof fuel (Solidity.Yul.LocalState.ofClean (locals,world)) =
                  (.ok (.clean (.bool value)),Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld)) at expression
                rw [Solidity.Yul.LocalBoolInitialization.run,expression] at declaration
                have encoded : Solidity.Yul.LocalBoolInitialization.project
                  (Solidity.Yul.LocalBoolInitialization.finish
                    (.ok (.clean (.bool value)),Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld))) =
                  some (.ok (.normal (Solidity.Source.Locals.cons (.bool value) nextLocals)),
                    (Solidity.Source.L0 env,nextWorld)) := by
                  change (Solidity.Yul.LocalValues.clean? (.bool :: types)
                    (Solidity.Yul.LocalValues.ofClean (Solidity.Source.Locals.cons (.bool value) nextLocals))).map
                    (fun finalLocals =>
                      ((Except.ok (Solidity.Source.Out.normal finalLocals) :
                        Solidity.Source.R (Solidity.Source.Out env.layout types (.bool :: types))),
                        (Solidity.Source.L0 env,nextWorld))) = _
                  rw [Solidity.Yul.LocalValues.clean_ofClean]
                  rfl
                rw [encoded] at declaration
                have child := (Option.some.inj declaration).symm
                have items : (Solidity.Source.execItems glob frame (fuel+2) nps ph
                  (.stmt (Solidity.Source.RStmt.declInit (R := returns) (M := modifier) (k := control)
                    (τ := .bool) expr (by rfl)) .nil) locals).run (Solidity.Source.L0 env,world) =
                  (.ok (.normal (Solidity.Source.Locals.cons (.bool value) nextLocals)),
                    (Solidity.Source.L0 env,nextWorld)) := by
                  rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,child]
                  rfl
                simp only [Solidity.Yul.LocalBoolScope.run,Solidity.Yul.LocalBoolInitialization.run,expression,
                  Solidity.Yul.LocalBoolInitialization.finish,Solidity.Yul.LocalBoolScope.close,Solidity.Yul.LocalBoolScope.project]
                rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,items]
                dsimp only [Solidity.Yul.LocalState.ofClean]
                rw [Solidity.Yul.LocalValues.clean_ofClean]
                change some (.ok (.normal nextLocals),(Solidity.Source.L0 env,nextWorld)) =
                  some ((Solidity.Source.EM.lift
                    ((Solidity.Source.Out.normal (Solidity.Source.Locals.cons (.bool value) nextLocals) :
                      Solidity.Source.Out env.layout types (.bool :: types)).close)).run
                    (Solidity.Source.L0 env,nextWorld))
                rw [Solidity.Source.Out.close,Solidity.Yul.RawLocalScope.restore_cons]
                rfl
              | memRef impossible _ => cases impossible
              | storRef impossible _ => cases impossible
              | cdRef impossible _ => cases impossible


end Solidity.Yul.LocalBoolScope
