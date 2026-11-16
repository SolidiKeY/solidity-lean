import Solidity.Yul.LocalCompareControl

/-! Actual Source expression statements over bool LOCAL consumers. The LOCAL
runner retains partial locals on every halt; projection matches Source.execS's
actual EM.sub boundary, which exposes those locals only on normal completion.
No new Source statement constructor, raw frame/session policy or admission. -/
namespace Solidity.Yul.LocalExprStatement

def discard {env ctx}
    (expression : Nat → LocalState env ctx →
      Solidity.Source.R (LocalValue env .bool) × LocalState env ctx)
    (fuel : Nat) (state : LocalState env ctx) :
    Solidity.Source.R Unit × LocalState env ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | fuel+1 =>
      let (result,next) := expression fuel state
      (result.map (fun _ => ()),next)

theorem discard_step {env ctx}
    (expression : Nat → LocalState env ctx →
      Solidity.Source.R (LocalValue env .bool) × LocalState env ctx)
    (fuel : Nat) (state : LocalState env ctx) :
    discard expression (fuel+1) state =
      (let (result,next) := expression fuel state
       (result.map (fun _ => ()),next)) := rfl

/-- Exact old Source statement observation. Raw locals are not implicitly
cleaned. A halt retains LOCAL locals in discard's result; old EM.sub does not
expose them, whereas normal completion requires genuinely clean locals. -/
def project {env ctx} (result : Solidity.Source.R Unit × LocalState env ctx) :
    Option (Solidity.Source.R (Solidity.Source.Out env.layout ctx ctx) ×
      (Solidity.Source.Locals env.layout [] × Solidity.Source.St env)) :=
  match result.1 with
  | .error halt => some (.error halt,(Solidity.Source.L0 env,result.2.2))
  | .ok _ => (LocalValues.clean? ctx result.2.1).map
      (fun locals => (.ok (.normal locals),(Solidity.Source.L0 env,result.2.2)))

theorem source_step {env ctx} (expr : Solidity.Source.RExpr env ctx .bool)
    (expression : Nat → LocalState env ctx →
      Solidity.Source.R (LocalValue env .bool) × LocalState env ctx)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
    (agreement : ∀ state, expression fuel (LocalState.ofClean state) =
      LocalBoolExpr.cleanOutcome ((Solidity.Source.evalE glob frame fuel expr).run state))
    (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
    (locals : Solidity.Source.Locals env.layout ctx) (world : Solidity.Source.St env) :
    project (discard expression (fuel+1) (LocalState.ofClean (locals,world))) =
      some ((Solidity.Source.execS glob frame (fuel+1) nps ph
        (Solidity.Source.RStmt.expr (R := returns) (M := modifier) (k := control) expr) locals).run
          (Solidity.Source.L0 env,world)) := by
  have agrees := agreement (locals,world)
  cases actual : (Solidity.Source.evalE glob frame fuel expr).run (locals,world) with
  | mk result next =>
      rcases next with ⟨nextLocals,nextWorld⟩
      let next := (nextLocals,nextWorld)
      rw [actual] at agrees
      cases result with
      | error halt =>
          change expression fuel (LocalState.ofClean (locals,world)) =
            (.error halt,LocalState.ofClean next) at agrees
          rw [discard_step,agrees]
          have sub : (Solidity.Source.EM.sub (Γ := []) locals
              (Solidity.Source.evalE glob frame fuel expr)).run (Solidity.Source.L0 env,world) =
                (.error halt,(Solidity.Source.L0 env,next.2)) := by
            have actualRun : Solidity.Source.evalE (plan := none) (calldataKnown := true) glob frame fuel expr (locals,world) =
                (.error halt,(nextLocals,nextWorld)) := actual
            simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
            rfl
          rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub]
          rfl
      | ok value =>
          cases value with
          | val value =>
              cases value with
              | bool value =>
                  change expression fuel (LocalState.ofClean (locals,world)) =
                    (.ok (.clean (.bool value)),LocalState.ofClean next) at agrees
                  rw [discard_step,agrees]
                  have sub : (Solidity.Source.EM.sub (Γ := []) locals
                      (Solidity.Source.evalE glob frame fuel expr)).run (Solidity.Source.L0 env,world) =
                        (.ok (.val (.bool value),next.1),(Solidity.Source.L0 env,next.2)) := by
                    have actualRun : Solidity.Source.evalE (plan := none) (calldataKnown := true) glob frame fuel expr (locals,world) =
                        (.ok (.val (.bool value)),(nextLocals,nextWorld)) := actual
                    simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
                    rfl
                  rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub]
                  simp only [Except.map,project,LocalState.ofClean,LocalValues.clean_ofClean]
                  rfl
              | memRef impossible _ => cases impossible
              | storRef impossible _ => cases impossible
              | cdRef impossible _ => cases impossible

/-- Concrete all-tree/all-horizon bool-control statement equality, with no
assumed child law. Normal outputs and entire old Source.St are exact. -/
theorem bool_source_agrees {env ctx expr} (proof : LocalBoolControl.Supported env ctx expr)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
    (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
    (locals : Solidity.Source.Locals env.layout ctx) (world : Solidity.Source.St env) :
    project (discard (LocalBoolControl.eval proof) fuel (LocalState.ofClean (locals,world))) =
      some ((Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.expr (R := returns) (M := modifier) (k := control) expr) locals).run
          (Solidity.Source.L0 env,world)) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      exact source_step expr (LocalBoolControl.eval proof) glob frame fuel nps ph
        (LocalBoolControl.source_agrees proof glob frame fuel) returns modifier control locals world

/-- Concrete comparison-selected expression statement. Checked is a REAL
operand-add premise, not a generic Source statement requirement. -/
theorem compare_source_agrees {env ctx left right yes no} (op : Solidity.Source.BinOp)
    (one : LocalU8Expr.Supported env ctx left) (two : LocalU8Expr.Supported env ctx right)
    (yesProof : LocalBoolControl.Supported env ctx yes)
    (noProof : LocalBoolControl.Supported env ctx no)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
    (checked : frame.checked = true) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
    (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
    (locals : Solidity.Source.Locals env.layout ctx) (world : Solidity.Source.St env) :
    project (discard (LocalCompareControl.eval op one two yesProof noProof glob.pipeline)
      fuel (LocalState.ofClean (locals,world))) =
      some ((Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.expr (R := returns) (M := modifier) (k := control)
          (.cond (.compare op left right) yes no)) locals).run (Solidity.Source.L0 env,world)) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      exact source_step _ _ glob frame fuel nps ph
        (LocalCompareControl.source_agrees op one two yesProof noProof glob frame checked fuel)
        returns modifier control locals world

end Solidity.Yul.LocalExprStatement
