import Solidity.Yul.LocalBoolIf
import Solidity.Yul.RawSequence

/-! Fuelled iteration of an actual Source Boolean condition and certified item scope.
Scope-local declarations are restored after each successful iteration. -/
namespace Solidity.Yul.LocalBoolWhile

def run {env returns modifier types out condition u items}
    (test : LocalBoolControl.Supported env types condition)
    (body : LocalBoolItems.Supported env returns modifier ⟨true,u⟩
      (types := types) (out := out) items) :
    Nat → LocalState env types → LocalBoolItems.Result env types
  | 0, state => .halted .timeout state
  | fuel+1, state =>
    let actual := LocalBoolControl.eval test fuel state
    match actual.1 with
    | .error halt => .halted halt actual.2
    | .ok value =>
      if LocalBoolControl.truth value then
        LocalBoolItems.Result.casesOn
          (motive := fun _ => LocalBoolItems.Result env types)
          (LocalBoolItemScope.run body fuel actual.2)
          (fun next => run test body fuel next)
          (fun {_reached} halt next => .halted halt next)
      else .normal actual.2

/-- Actual Source agreement for certified scoped bodies, from completely clean input.
This does not assert dirty Source or compiler adequacy. -/
theorem source_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (l u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (branch : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalBoolWhile.run test branch fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph (.whileLoop (l := l) condition (.block items)) locals).run
   (Solidity.Source.L0 env,world)) := by

  intro env returns modifier l u types out condition test items branch glob frame fuel nps ph locals world
  induction fuel generalizing locals world with
  | zero => rfl
  | succ fuel ih =>
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
          have actualRun : Solidity.Source.evalE (plan := none) (calldataKnown := true) glob frame fuel condition (locals,world) =
            (.error halt,(nextLocals,nextWorld)) := actual
          simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
        simp only [Solidity.Yul.LocalBoolWhile.run,expression,Solidity.Yul.LocalBoolItems.project]
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
              have actualRun : Solidity.Source.evalE (plan := none) (calldataKnown := true) glob frame fuel condition (locals,world) =
                (.ok (.val (.bool value)),(nextLocals,nextWorld)) := actual
              simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
            cases value with
            | false =>
              rw [Solidity.Yul.LocalBoolWhile.run,expression]
              simp only [Solidity.Yul.LocalBoolControl.truth_clean,
                Solidity.Yul.LocalBoolItems.project,Solidity.Yul.LocalState.ofClean,
                Solidity.Yul.LocalValues.clean_ofClean,Option.map_some,Bool.false_eq_true,if_false]
              rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub] <;> rfl
            | true =>
              simp only [Solidity.Yul.LocalBoolWhile.run,expression,Solidity.Yul.LocalBoolControl.truth_clean]
              rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub]
              dsimp only []
              rw [Solidity.Source.Hoare.run_bind]
              have getTrue : (Solidity.Source.getV (E := env) (Γ := [])
                  (Solidity.Source.RVal.val (Solidity.Source.Val.bool true))).run
                  (Solidity.Source.L0 env,nextWorld) =
                  (.ok (.bool true),(Solidity.Source.L0 env,nextWorld)) := by rfl
              rw [getTrue]
              dsimp only []
              have scopeAgreement := Solidity.Yul.LocalBoolItemScope.source_agrees env returns modifier ⟨true,u⟩
                types out items branch glob frame fuel nps ph nextLocals nextWorld
              cases branchRun : Solidity.Yul.LocalBoolItemScope.run branch fuel
                (Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld)) with
              | halted halt final =>
                rw [branchRun] at scopeAgreement
                change some ((Except.error halt : Solidity.Source.R
                  (Solidity.Source.Out env.layout types types)),(Solidity.Source.L0 env,final.2)) = some _ at scopeAgreement
                have child := (Option.some.inj scopeAgreement).symm
                simp only [if_true,Solidity.Yul.LocalBoolItems.project]
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
                  simp only [if_true]
                  rw [Solidity.Source.Hoare.run_bind,child]
                  have rebuilt := Solidity.Yul.LocalBoolItemScope.values_inverse env types final.1 finalLocals decoded
                  have stateBack : Solidity.Yul.LocalState.ofClean (finalLocals,final.2) = final := by
                    cases final
                    simp only [Solidity.Yul.LocalState.ofClean]
                    rw [rebuilt]
                  dsimp only []
                  rw [Solidity.Yul.RawSequence.restore_self]
                  change Solidity.Yul.LocalBoolItems.project types
                    (Solidity.Yul.LocalBoolWhile.run test branch fuel final) =
                    some ((Solidity.Source.execS glob frame fuel nps ph
                      (.whileLoop (l := l) condition (.block items)) finalLocals).run
                      (Solidity.Source.L0 env,final.2))
                  rw [← stateBack]
                  exact ih finalLocals final.2
          | memRef impossible _ => cases impossible
          | storRef impossible _ => cases impossible
          | cdRef impossible _ => cases impossible


end Solidity.Yul.LocalBoolWhile
