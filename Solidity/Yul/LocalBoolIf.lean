import Solidity.Yul.LocalBoolItemScope

/-! Conditional execution of a concrete certified Boolean item scope.
Condition and branch partial effects retain their actual reached contexts. -/
namespace Solidity.Yul.LocalBoolIf

def run {env returns modifier control types out condition items}
    (test : LocalBoolControl.Supported env types condition)
    (branch : LocalBoolItems.Supported env returns modifier control (types := types) (out := out) items)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env types :=
  match fuel with
  | 0 => .halted .timeout state
  | fuel+1 =>
    let actual := LocalBoolControl.eval test fuel state
    match actual.1 with
    | .error halt => .halted halt actual.2
    | .ok value =>
      if LocalBoolControl.truth value then LocalBoolItemScope.run branch fuel actual.2
      else .normal actual.2



theorem restore_self : ∀ (layout : Solidity.Source.Layout) (types : Solidity.Source.RCtx)
 (locals : Solidity.Source.Locals layout types), locals.restore types = .ok locals := by
  intro layout types locals
  unfold Solidity.Source.Locals.restore
  have same : types.drop (types.length - types.length) = types := by
    rw [Nat.sub_self]
    rfl
  rw [dif_pos same]
  have dropped : ∀ (count : Nat) (zero : count = 0) (back : types.drop count = types),
      (back ▸ Solidity.Source.Locals.drop count locals) = locals := by
    intro count zero back
    subst count
    rfl
  rw [dropped _ (Nat.sub_self _) same] <;> rfl


/-- Agreement with the existing Source conditional, from a completely clean input frame.
Dirty execution is retained by run; this theorem does not assert its Source adequacy. -/
theorem source_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (branch : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalBoolIf.run test branch fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph (.ifThen condition (.block items)) locals).run
   (Solidity.Source.L0 env,world)) := by

  intro env returns modifier control types out condition test items branch glob frame fuel nps ph locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have expression := Solidity.Yul.LocalBoolControl.source_agrees test glob frame fuel (locals,world)
    cases actual : (Solidity.Source.evalE glob frame fuel condition).run (locals,world) with
    | mk result next =>
      rcases next with ⟨nextLocals,nextWorld⟩
      rw [actual] at expression
      cases result with
      | error halt =>
        change Solidity.Yul.LocalBoolControl.eval test fuel (Solidity.Yul.LocalState.ofClean (locals,world)) =
          (.error halt,Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld)) at expression
        have sub : (Solidity.Source.EM.sub (Γ := []) locals
          (Solidity.Source.evalE glob frame fuel condition)).run (Solidity.Source.L0 env,world) =
          (.error halt,(Solidity.Source.L0 env,nextWorld)) := by
          have actualRun : Solidity.Source.evalE (plan := none) glob frame fuel condition (locals,world) =
            (.error halt,(nextLocals,nextWorld)) := actual
          simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
        simp only [Solidity.Yul.LocalBoolIf.run,expression,Solidity.Yul.LocalBoolItems.project]
        rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub] <;> rfl
      | ok value =>
        cases value with
        | val value =>
          cases value with
          | bool value =>
            change Solidity.Yul.LocalBoolControl.eval test fuel (Solidity.Yul.LocalState.ofClean (locals,world)) =
              (.ok (.clean (.bool value)),Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld)) at expression
            have sub : (Solidity.Source.EM.sub (Γ := []) locals
              (Solidity.Source.evalE glob frame fuel condition)).run (Solidity.Source.L0 env,world) =
              (.ok (.val (.bool value),nextLocals),(Solidity.Source.L0 env,nextWorld)) := by
              have actualRun : Solidity.Source.evalE (plan := none) glob frame fuel condition (locals,world) =
                (.ok (.val (.bool value)),(nextLocals,nextWorld)) := actual
              simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
            cases value with
            | false =>
              rw [Solidity.Yul.LocalBoolIf.run,expression]
              simp only [Solidity.Yul.LocalBoolControl.truth_clean,
                Solidity.Yul.LocalBoolItems.project,Solidity.Yul.LocalState.ofClean,
                Solidity.Yul.LocalValues.clean_ofClean,Option.map_some,Bool.false_eq_true,if_false]
              rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub] <;> rfl
            | true =>
              simp only [Solidity.Yul.LocalBoolIf.run,expression,Solidity.Yul.LocalBoolControl.truth_clean]
              rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub]
              change Solidity.Yul.LocalBoolItems.project types
                (Solidity.Yul.LocalBoolItemScope.run branch fuel
                  (Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld))) =
                some ((do
                  let outcome ← Solidity.Source.execS glob frame fuel nps ph (.block items) nextLocals
                  Solidity.Source.EM.lift outcome.close).run (Solidity.Source.L0 env,nextWorld))
              have scopeAgreement := Solidity.Yul.LocalBoolItemScope.source_agrees env returns modifier control
                types out items branch glob frame fuel nps ph nextLocals nextWorld
              cases branchRun : Solidity.Yul.LocalBoolItemScope.run branch fuel
                (Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld)) with
              | halted halt final =>
                rw [branchRun] at scopeAgreement
                change some ((Except.error halt : Solidity.Source.R
                  (Solidity.Source.Out env.layout types types)),(Solidity.Source.L0 env,final.2)) = some _ at scopeAgreement
                have child := (Option.some.inj scopeAgreement).symm
                simp only [Solidity.Yul.LocalBoolItems.project]
                rw [Solidity.Source.Hoare.run_bind,child] <;> rfl
              | normal final =>
                rw [branchRun] at scopeAgreement
                cases decoded : Solidity.Yul.LocalValues.clean? types final.1 with
                | none =>
                  simp only [Solidity.Yul.LocalBoolItems.project,decoded,Option.map_none] at scopeAgreement
                  cases scopeAgreement
                | some finalLocals =>
                  simp only [Solidity.Yul.LocalBoolItems.project,decoded,Option.map_some] at scopeAgreement
                  have child := (Option.some.inj scopeAgreement).symm
                  simp only [Solidity.Yul.LocalBoolItems.project,decoded,Option.map_some]
                  rw [Solidity.Source.Hoare.run_bind,child]
                  dsimp only []
                  rw [Solidity.Source.Out.close,Solidity.Yul.LocalBoolIf.restore_self] <;> rfl
          | memRef impossible _ => cases impossible
          | storRef impossible _ => cases impossible
          | cdRef impossible _ => cases impossible


end Solidity.Yul.LocalBoolIf
