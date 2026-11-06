import Solidity.Yul.LocalBoolInitialization

/-! One Boolean declaration followed by an expression in its extended context.
Failure stages retain their reached intrinsic context and complete partial state. -/
namespace Solidity.Yul.LocalBoolBinding

inductive Result (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) where
  | normal : LocalState env (.bool :: types) → Result env types
  | initialHalt : Solidity.Source.Halt → LocalState env types → Result env types
  | bodyHalt : Solidity.Source.Halt → LocalState env (.bool :: types) → Result env types

def tail {env types expr} (proof : LocalBoolControl.Supported env types expr)
    (fuel : Nat) (state : LocalState env types) :
    Solidity.Source.R Unit × LocalState env types :=
  match fuel with
  | 0 => (.error .timeout,state)
  | fuel+1 =>
    let actual := LocalExprStatement.discard (LocalBoolControl.eval proof) fuel state
    match actual.1 with
    | .error halt => (.error halt,actual.2)
    | .ok _ => match fuel with
      | 0 => (.error .timeout,actual.2)
      | _+1 => (.ok (),actual.2)

def finish {env types} (actual : Solidity.Source.R Unit × LocalState env (.bool :: types)) :
    Result env types :=
  match actual.1 with
  | .error halt => .bodyHalt halt actual.2
  | .ok _ => .normal actual.2

def run {env types init body}
    (first : LocalBoolControl.Supported env types init)
    (second : LocalBoolControl.Supported env (.bool :: types) body)
    (fuel : Nat) (state : LocalState env types) : Result env types :=
  match fuel with
  | 0 => .initialHalt .timeout state
  | fuel+1 => LocalBoolInitialization.Result.casesOn
      (motive := fun _ => Result env types)
      (LocalBoolInitialization.run first fuel state)
      (fun extended => finish (tail second fuel extended))
      (fun halt previous => .initialHalt halt previous)

def project {env types} (result : Result env types) :
    Option (Solidity.Source.R (Solidity.Source.Out env.layout types (.bool :: types)) ×
      (Solidity.Source.Locals env.layout [] × Solidity.Source.St env)) :=
  Result.casesOn (motive := fun _ => Option
    (Solidity.Source.R (Solidity.Source.Out env.layout types (.bool :: types)) ×
      (Solidity.Source.Locals env.layout [] × Solidity.Source.St env))) result
    (fun next => (LocalValues.clean? (.bool :: types) next.1).map
      (fun locals => (.ok (.normal locals),(Solidity.Source.L0 env,next.2))))
    (fun halt next => some (.error halt,(Solidity.Source.L0 env,next.2)))
    (fun halt next => some (.error halt,(Solidity.Source.L0 env,next.2)))



theorem tail_source_agrees : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env types .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported env types expr)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalExprStatement.project
   (Solidity.Yul.LocalBoolBinding.tail proof fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execItems glob frame fuel nps ph
   (.stmt (Solidity.Source.RStmt.expr (R := returns) (M := modifier) (k := control) expr) .nil)
   locals).run (Solidity.Source.L0 env,world)) := by
  intro env types expr proof glob frame fuel nps ph returns modifier control locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      have agrees := Solidity.Yul.LocalExprStatement.bool_source_agrees proof glob frame
        (fuel+1) nps ph returns modifier control locals world
      cases actual : Solidity.Yul.LocalExprStatement.discard
        (Solidity.Yul.LocalBoolControl.eval proof) (fuel+1)
        (Solidity.Yul.LocalState.ofClean (locals,world)) with
      | mk result next =>
        rcases next with ⟨nextLocals,nextWorld⟩
        rw [actual] at agrees
        cases result with
        | error halt =>
          change some ((Except.error halt : Solidity.Source.R
            (Solidity.Source.Out env.layout types types)),(Solidity.Source.L0 env,nextWorld)) = some _ at agrees
          have child := (Option.some.inj agrees).symm
          simp only [Solidity.Yul.LocalBoolBinding.tail,actual,Solidity.Yul.LocalExprStatement.project]
          rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,child] <;> rfl
        | ok value =>
          cases value
          cases decoded : Solidity.Yul.LocalValues.clean? types nextLocals with
          | none =>
            simp only [Solidity.Yul.LocalExprStatement.project,decoded,Option.map_none] at agrees
            cases agrees
          | some cleanLocals =>
            simp only [Solidity.Yul.LocalExprStatement.project,decoded,Option.map_some] at agrees
            have child := (Option.some.inj agrees).symm
            simp only [Solidity.Yul.LocalBoolBinding.tail,actual,Solidity.Yul.LocalExprStatement.project,
              decoded,Option.map_some]
            rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,child] <;> rfl




theorem source_agrees : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (body : Solidity.Source.RExpr env (.bool :: types) .bool)
 (first : Solidity.Yul.LocalBoolControl.Supported env types init)
 (second : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) body)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolBinding.project
   (Solidity.Yul.LocalBoolBinding.run first second fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execItems glob frame fuel nps ph
   (.stmt (Solidity.Source.RStmt.declInit (R := returns) (M := modifier) (k := control)
     (τ := .bool) init (by rfl))
     (.stmt (Solidity.Source.RStmt.expr body) .nil))
   locals).run (Solidity.Source.L0 env,world)) := by
  intro env types init body first second glob frame fuel nps ph returns modifier control locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      have expression := Solidity.Yul.LocalBoolControl.source_agrees first glob frame fuel (locals,world)
      have declaration := Solidity.Yul.LocalBoolInitialization.source_agrees env types init first
        glob frame (fuel+1) nps ph returns modifier control locals world
      cases actual : (Solidity.Source.evalE glob frame fuel init).run (locals,world) with
      | mk result next =>
        rcases next with ⟨nextLocals,nextWorld⟩
        rw [actual] at expression
        cases result with
        | error halt =>
          change Solidity.Yul.LocalBoolControl.eval first fuel (Solidity.Yul.LocalState.ofClean (locals,world)) =
            (.error halt,Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld)) at expression
          rw [Solidity.Yul.LocalBoolInitialization.run,expression] at declaration
          change some ((Except.error halt : Solidity.Source.R
            (Solidity.Source.Out env.layout types (.bool :: types))),
            (Solidity.Source.L0 env,nextWorld)) = some _ at declaration
          have child := (Option.some.inj declaration).symm
          simp only [Solidity.Yul.LocalBoolBinding.run,Solidity.Yul.LocalBoolInitialization.run,expression,
            Solidity.Yul.LocalBoolInitialization.finish,Solidity.Yul.LocalBoolBinding.project]
          rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,child] <;> rfl
        | ok value =>
          cases value with
          | val value =>
            cases value with
            | bool value =>
              change Solidity.Yul.LocalBoolControl.eval first fuel (Solidity.Yul.LocalState.ofClean (locals,world)) =
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
              have firstEq : Solidity.Yul.LocalBoolInitialization.run first (fuel+1)
                (Solidity.Yul.LocalState.ofClean (locals,world)) =
                .normal (Solidity.Yul.LocalState.ofClean
                  (Solidity.Source.Locals.cons (.bool value) nextLocals,nextWorld)) := by
                rw [Solidity.Yul.LocalBoolInitialization.run,expression]
                rfl
              have following := Solidity.Yul.LocalBoolBinding.tail_source_agrees env (.bool :: types)
                body second glob frame (fuel+1) nps ph returns modifier control
                (Solidity.Source.Locals.cons (.bool value) nextLocals) nextWorld
              cases after : Solidity.Yul.LocalBoolBinding.tail second (fuel+1)
                (Solidity.Yul.LocalState.ofClean
                  (Solidity.Source.Locals.cons (.bool value) nextLocals,nextWorld)) with
              | mk outcome final =>
                rcases final with ⟨finalValues,finalWorld⟩
                rw [after] at following
                cases outcome with
                | error halt =>
                  change some ((Except.error halt : Solidity.Source.R
                    (Solidity.Source.Out env.layout (.bool :: types) (.bool :: types))),
                    (Solidity.Source.L0 env,finalWorld)) = some _ at following
                  have tailChild := (Option.some.inj following).symm
                  simp only [Solidity.Yul.LocalBoolBinding.run,firstEq,after,
                    Solidity.Yul.LocalBoolBinding.finish,Solidity.Yul.LocalBoolBinding.project]
                  rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,child]
                  dsimp only []
                  rw [Solidity.Source.Hoare.run_bind,tailChild] <;> rfl
                | ok unit =>
                  cases unit
                  cases decoded : Solidity.Yul.LocalValues.clean? (.bool :: types) finalValues with
                  | none =>
                    simp only [Solidity.Yul.LocalExprStatement.project,decoded,Option.map_none] at following
                    cases following
                  | some finalLocals =>
                    simp only [Solidity.Yul.LocalExprStatement.project,decoded,Option.map_some] at following
                    have tailChild := (Option.some.inj following).symm
                    simp only [Solidity.Yul.LocalBoolBinding.run,firstEq,after,
                      Solidity.Yul.LocalBoolBinding.finish,Solidity.Yul.LocalBoolBinding.project,
                      decoded,Option.map_some]
                    rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,child]
                    dsimp only []
                    rw [Solidity.Source.Hoare.run_bind,tailChild] <;> rfl
            | memRef impossible _ => cases impossible
            | storRef impossible _ => cases impossible
            | cdRef impossible _ => cases impossible


end Solidity.Yul.LocalBoolBinding
