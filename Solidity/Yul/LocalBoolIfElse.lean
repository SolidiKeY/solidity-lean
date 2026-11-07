import Solidity.Yul.LocalBoolIf

/-! Concrete conditional selection between two independently indexed item scopes.
Raw condition and branch effects retain the actual reached context. -/
namespace Solidity.Yul.LocalBoolIfElse

def run {env returns modifier control types yesOut noOut condition yesItems noItems}
    (test : LocalBoolControl.Supported env types condition)
    (yes : LocalBoolItems.Supported env returns modifier control
      (types := types) (out := yesOut) yesItems)
    (no : LocalBoolItems.Supported env returns modifier control
      (types := types) (out := noOut) noItems)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env types :=
  match fuel with
  | 0 => .halted .timeout state
  | fuel+1 =>
    let actual := LocalBoolControl.eval test fuel state
    match actual.1 with
    | .error halt => .halted halt actual.2
    | .ok value =>
      if LocalBoolControl.truth value then LocalBoolItemScope.run yes fuel actual.2
      else LocalBoolItemScope.run no fuel actual.2

/-- Concrete Source agreement from a completely clean frame; no dirty Source adequacy is asserted. -/
theorem source_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types yesOut noOut : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (yesItems : Solidity.Source.RItems env returns modifier control types yesOut)
 (yes : Solidity.Yul.LocalBoolItems.Supported env returns modifier control yesItems)
 (noItems : Solidity.Source.RItems env returns modifier control types noOut)
 (no : Solidity.Yul.LocalBoolItems.Supported env returns modifier control noItems)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalBoolIfElse.run test yes no fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph (.ifElse condition (.block yesItems) (.block noItems)) locals).run
   (Solidity.Source.L0 env,world)) := by

  intro env returns modifier control types yesOut noOut condition test yesItems yes noItems no glob frame fuel nps ph locals world
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
        simp only [Solidity.Yul.LocalBoolIfElse.run,expression,Solidity.Yul.LocalBoolItems.project]
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
              simp only [Solidity.Yul.LocalBoolIfElse.run,expression,Solidity.Yul.LocalBoolControl.truth_clean,Bool.false_eq_true,if_false]
              rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub]
              change Solidity.Yul.LocalBoolItems.project types
                (Solidity.Yul.LocalBoolItemScope.run no fuel
                  (Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld))) =
                some ((do
                  let outcome ← Solidity.Source.execS glob frame fuel nps ph (.block noItems) nextLocals
                  Solidity.Source.EM.lift outcome.close).run (Solidity.Source.L0 env,nextWorld))
              have scopeAgreement := Solidity.Yul.LocalBoolItemScope.source_agrees env returns modifier control
                types noOut noItems no glob frame fuel nps ph nextLocals nextWorld
              cases branchRun : Solidity.Yul.LocalBoolItemScope.run no fuel
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
                  rw [Solidity.Source.Out.close,Solidity.Yul.RawSequence.restore_self] <;> rfl
            | true =>
              simp only [Solidity.Yul.LocalBoolIfElse.run,expression,Solidity.Yul.LocalBoolControl.truth_clean]
              rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub]
              change Solidity.Yul.LocalBoolItems.project types
                (Solidity.Yul.LocalBoolItemScope.run yes fuel
                  (Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld))) =
                some ((do
                  let outcome ← Solidity.Source.execS glob frame fuel nps ph (.block yesItems) nextLocals
                  Solidity.Source.EM.lift outcome.close).run (Solidity.Source.L0 env,nextWorld))
              have scopeAgreement := Solidity.Yul.LocalBoolItemScope.source_agrees env returns modifier control
                types yesOut yesItems yes glob frame fuel nps ph nextLocals nextWorld
              cases branchRun : Solidity.Yul.LocalBoolItemScope.run yes fuel
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
                  rw [Solidity.Source.Out.close,Solidity.Yul.RawSequence.restore_self] <;> rfl
          | memRef impossible _ => cases impossible
          | storRef impossible _ => cases impossible
          | cdRef impossible _ => cases impossible


end Solidity.Yul.LocalBoolIfElse
