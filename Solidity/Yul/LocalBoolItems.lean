import Solidity.Yul.LocalBoolBinding

/-! Intrinsic certificates for Boolean declaration/expression item lists.
Every halted state retains its reached context; existing Source syntax is unchanged. -/
namespace Solidity.Yul.LocalBoolItems

inductive Supported (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
    (modifier : Bool) (control : Solidity.Source.SCtx) :
    {types out : Solidity.Source.RCtx} →
    Solidity.Source.RItems env returns modifier control types out → Type where
  | nil {types} : Supported env returns modifier control (Solidity.Source.RItems.nil (Γ := types))
  | expression {types out expr rest} :
      LocalBoolControl.Supported env types expr →
      Supported env returns modifier control (types := types) (out := out) rest →
      Supported env returns modifier control (.stmt (.expr expr) rest)
  | declaration {types out init rest} :
      LocalBoolControl.Supported env types init →
      Supported env returns modifier control (types := .bool :: types) (out := out) rest →
      Supported env returns modifier control
        (.stmt (.declInit (τ := .bool) init (by rfl)) rest)

inductive Result (env : Solidity.Source.Env) (out : Solidity.Source.RCtx) where
  | normal : LocalState env out → Result env out
  | halted {reached : Solidity.Source.RCtx} :
      Solidity.Source.Halt → LocalState env reached → Result env out

def run {env returns modifier control types out items}
    (proof : Supported env returns modifier control (types := types) (out := out) items) :
    Nat → LocalState env types → Result env out := by
  apply Supported.casesOn (motive := fun {types out} _ _ =>
    Nat → LocalState env types → Result env out) proof
  case nil =>
    intro types
    exact fun fuel state => match fuel with
      | 0 => .halted .timeout state
      | _+1 => .normal state
  case expression =>
    intro types out expr rest one tail
    exact fun fuel state => match fuel with
      | 0 => .halted .timeout state
      | fuel+1 =>
        let actual := LocalExprStatement.discard (LocalBoolControl.eval one) fuel state
        match actual.1 with
        | .error halt => .halted halt actual.2
        | .ok _ => run tail fuel actual.2
  case declaration =>
    intro types out init rest one tail
    exact fun fuel state => match fuel with
      | 0 => .halted .timeout state
      | fuel+1 => LocalBoolInitialization.Result.casesOn
          (motive := fun _ => Result env out)
          (LocalBoolInitialization.run one fuel state)
          (fun next => run tail fuel next)
          (fun halt previous => .halted halt previous)
termination_by structural proof

def project {env out} (input : Solidity.Source.RCtx) (result : Result env out) :
    Option (Solidity.Source.R (Solidity.Source.Out env.layout input out) ×
      (Solidity.Source.Locals env.layout [] × Solidity.Source.St env)) :=
  Result.casesOn (motive := fun _ => Option
    (Solidity.Source.R (Solidity.Source.Out env.layout input out) ×
      (Solidity.Source.Locals env.layout [] × Solidity.Source.St env))) result
    (fun next => (LocalValues.clean? out next.1).map
      (fun locals => (.ok (.normal locals),(Solidity.Source.L0 env,next.2))))
    (fun {_reached} halt next => some (.error halt,(Solidity.Source.L0 env,next.2)))



theorem project_up : ∀ (env : Solidity.Source.Env) (input middle out : Solidity.Source.RCtx)
 (result : Solidity.Yul.LocalBoolItems.Result env out),
 Solidity.Yul.LocalBoolItems.project input result =
 (Solidity.Yul.LocalBoolItems.project middle result).map
   (fun observed => (observed.1.bind (fun outcome => outcome.up input),observed.2)) := by
  intro env input middle out result
  cases result with
  | normal next =>
    cases decoded : Solidity.Yul.LocalValues.clean? out next.1 with
    | none => simp only [Solidity.Yul.LocalBoolItems.project,decoded,Option.map_none]
    | some locals =>
      simp only [Solidity.Yul.LocalBoolItems.project,decoded,Option.map_some]
      rfl
  | halted halt next => rfl




theorem lift_up_run : ∀ (env : Solidity.Source.Env) (input middle out : Solidity.Source.RCtx)
 (action : Solidity.Source.EM env [] (Solidity.Source.Out env.layout middle out))
 (state : Solidity.Source.Locals env.layout [] × Solidity.Source.St env),
 (do let outcome ← action
     Solidity.Source.EM.lift (outcome.up input)).run state =
 (let actual := action.run state
  (actual.1.bind (fun outcome => outcome.up input),actual.2)) := by
  intro env input middle out action state
  rw [Solidity.Source.Hoare.run_bind]
  cases actual : action.run state with
  | mk result next =>
    cases result with
    | error halt => rfl
    | ok outcome =>
      cases moved : outcome.up input with
      | error halt => simp only [Except.bind,Solidity.Source.EM.lift,moved] <;> rfl
      | ok value => simp only [Except.bind,Solidity.Source.EM.lift,moved] <;> rfl




theorem source_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalBoolItems.run proof fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execItems glob frame fuel nps ph items locals).run
   (Solidity.Source.L0 env,world)) := by
  intro env returns modifier control types out items proof glob frame fuel nps ph locals world
  induction proof generalizing fuel world with
  | @nil types =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      simp only [Solidity.Yul.LocalBoolItems.run,Solidity.Yul.LocalBoolItems.project,
        Solidity.Yul.LocalState.ofClean,Solidity.Yul.LocalValues.clean_ofClean,Option.map_some]
      rfl
  | @expression types out expr rest one tail ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
        change Solidity.Yul.LocalBoolItems.project types
          (let actual := Solidity.Yul.LocalExprStatement.discard
             (Solidity.Yul.LocalBoolControl.eval one) (fuel+1)
             (Solidity.Yul.LocalState.ofClean (locals,world))
           match actual.1 with
           | .error halt => Solidity.Yul.LocalBoolItems.Result.halted halt actual.2
           | .ok _ => Solidity.Yul.LocalBoolItems.run tail (fuel+1) actual.2) = some _
        have expression := Solidity.Yul.LocalBoolControl.source_agrees one glob frame fuel (locals,world)
        have statement := Solidity.Yul.LocalExprStatement.bool_source_agrees one glob frame
          (fuel+1) nps ph returns modifier control locals world
        cases actual : (Solidity.Source.evalE glob frame fuel expr).run (locals,world) with
        | mk result next =>
          rcases next with ⟨nextLocals,nextWorld⟩
          rw [actual] at expression
          cases result with
          | error halt =>
            change Solidity.Yul.LocalBoolControl.eval one fuel (Solidity.Yul.LocalState.ofClean (locals,world)) =
              (.error halt,Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld)) at expression
            rw [Solidity.Yul.LocalExprStatement.discard_step,expression] at statement
            change some ((Except.error halt : Solidity.Source.R
              (Solidity.Source.Out env.layout types types)),(Solidity.Source.L0 env,nextWorld)) = some _ at statement
            have child := (Option.some.inj statement).symm
            simp only [Solidity.Yul.LocalExprStatement.discard_step,expression,Except.map]
            rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,child] <;> rfl
          | ok value =>
            cases value with
            | val value =>
              cases value with
              | bool value =>
                change Solidity.Yul.LocalBoolControl.eval one fuel (Solidity.Yul.LocalState.ofClean (locals,world)) =
                  (.ok (.clean (.bool value)),Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld)) at expression
                rw [Solidity.Yul.LocalExprStatement.discard_step,expression] at statement
                simp only [Except.map,Solidity.Yul.LocalExprStatement.project,
                  Solidity.Yul.LocalState.ofClean,Solidity.Yul.LocalValues.clean_ofClean,Option.map_some] at statement
                have child := (Option.some.inj statement).symm
                simp only [Solidity.Yul.LocalExprStatement.discard_step,expression,Except.map]
                change Solidity.Yul.LocalBoolItems.project types
                  (Solidity.Yul.LocalBoolItems.run tail (fuel+1)
                    (Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld))) = some _
                rw [Solidity.Yul.LocalBoolItems.project_up env types types out,
                  ih (fuel+1) nextLocals nextWorld]
                rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,child]
                dsimp only []
                rw [Solidity.Yul.LocalBoolItems.lift_up_run] <;> rfl
              | memRef impossible _ => cases impossible
              | storRef impossible _ => cases impossible
              | cdRef impossible _ => cases impossible
  | @declaration types out init rest one tail ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
        change Solidity.Yul.LocalBoolItems.project types
          (Solidity.Yul.LocalBoolInitialization.Result.casesOn
            (motive := fun _ => Solidity.Yul.LocalBoolItems.Result env out)
            (Solidity.Yul.LocalBoolInitialization.run one (fuel+1)
              (Solidity.Yul.LocalState.ofClean (locals,world)))
            (fun next => Solidity.Yul.LocalBoolItems.run tail (fuel+1) next)
            (fun halt previous => Solidity.Yul.LocalBoolItems.Result.halted halt previous)) = some _
        have expression := Solidity.Yul.LocalBoolControl.source_agrees one glob frame fuel (locals,world)
        have declaration := Solidity.Yul.LocalBoolInitialization.source_agrees env types init one
          glob frame (fuel+1) nps ph returns modifier control locals world
        cases actual : (Solidity.Source.evalE glob frame fuel init).run (locals,world) with
        | mk result next =>
          rcases next with ⟨nextLocals,nextWorld⟩
          rw [actual] at expression
          cases result with
          | error halt =>
            change Solidity.Yul.LocalBoolControl.eval one fuel (Solidity.Yul.LocalState.ofClean (locals,world)) =
              (.error halt,Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld)) at expression
            rw [Solidity.Yul.LocalBoolInitialization.run,expression] at declaration
            change some ((Except.error halt : Solidity.Source.R
              (Solidity.Source.Out env.layout types (.bool :: types))),
              (Solidity.Source.L0 env,nextWorld)) = some _ at declaration
            have child := (Option.some.inj declaration).symm
            rw [Solidity.Yul.LocalBoolInitialization.run,expression]
            rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,child] <;> rfl
          | ok value =>
            cases value with
            | val value =>
              cases value with
              | bool value =>
                change Solidity.Yul.LocalBoolControl.eval one fuel (Solidity.Yul.LocalState.ofClean (locals,world)) =
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
                rw [Solidity.Yul.LocalBoolInitialization.run,expression]
                change Solidity.Yul.LocalBoolItems.project types
                  (Solidity.Yul.LocalBoolItems.run tail (fuel+1)
                    (Solidity.Yul.LocalState.ofClean
                      (Solidity.Source.Locals.cons (.bool value) nextLocals,nextWorld))) = some _
                rw [Solidity.Yul.LocalBoolItems.project_up env types (.bool :: types) out,
                  ih (fuel+1) (Solidity.Source.Locals.cons (.bool value) nextLocals) nextWorld]
                rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,child]
                dsimp only []
                rw [Solidity.Yul.LocalBoolItems.lift_up_run] <;> rfl
              | memRef impossible _ => cases impossible
              | storRef impossible _ => cases impossible
              | cdRef impossible _ => cases impossible


end Solidity.Yul.LocalBoolItems
