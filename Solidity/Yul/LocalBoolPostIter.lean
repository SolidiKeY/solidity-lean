import Solidity.Yul.LocalBoolWhile

/-! Actual for iterations with certified Boolean guard/post and context-growing item body. -/
namespace Solidity.Yul.LocalBoolPostIter

def run {env returns modifier types out condition post u items}
    (test : LocalBoolControl.Supported env types condition)
    (step : LocalBoolControl.Supported env types post)
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
        LocalBoolItems.Result.casesOn (motive := fun _ => LocalBoolItems.Result env types)
          (LocalBoolItemScope.run body fuel actual.2)
          (fun next =>
            let updated := LocalBoolControl.eval step fuel next
            match updated.1 with
            | .error halt => .halted halt updated.2
            | .ok _ => run test step body fuel updated.2)
          (fun {_reached} halt next => .halted halt next)
      else .normal actual.2
/-- Concrete Source.forIter equality for present Boolean guard/post and certified scope.
Requires completely clean input; post values are discarded, not tested for truth. -/
theorem source_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (post : Solidity.Source.RExpr env types .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env types post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (branch : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalBoolPostIter.run test step branch fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.forIter glob frame fuel nps ph (.some condition) (.some post) (.block items) locals).run
   (Solidity.Source.L0 env,world)) := by


  intro env returns modifier u types out condition test post step items branch glob frame fuel nps ph locals world
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
        simp only [Solidity.Yul.LocalBoolPostIter.run,expression,Solidity.Yul.LocalBoolItems.project]
        rw [Solidity.Source.forIter]
        simp only [pure_bind]
        rw [Solidity.Source.Hoare.run_bind,sub] <;> rfl
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
              rw [Solidity.Yul.LocalBoolPostIter.run,expression]
              simp only [Solidity.Yul.LocalBoolControl.truth_clean,
                Solidity.Yul.LocalBoolItems.project,Solidity.Yul.LocalState.ofClean,
                Solidity.Yul.LocalValues.clean_ofClean,Option.map_some,Bool.false_eq_true,if_false]
              rw [Solidity.Source.forIter]
              simp only [pure_bind]
              rw [Solidity.Source.Hoare.run_bind,sub] <;> rfl
            | true =>
              simp only [Solidity.Yul.LocalBoolPostIter.run,expression,Solidity.Yul.LocalBoolControl.truth_clean]
              rw [Solidity.Source.forIter]
              simp only [pure_bind]
              rw [Solidity.Source.Hoare.run_bind,sub]
              dsimp only []
              rw [Solidity.Source.Hoare.run_bind]
              have getTrue : (Solidity.Source.getV (E := env) (Γ := [])
                  (Solidity.Source.RVal.val (Solidity.Source.Val.bool true))).run
                  (Solidity.Source.L0 env,nextWorld) =
                  (.ok (.bool true),(Solidity.Source.L0 env,nextWorld)) := by rfl
              rw [getTrue]
              simp only [Bool.not_true,Bool.false_eq_true,if_false,if_true]
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
                  simp only [Solidity.Source.EM.lift,pure_bind]
                  rw [← stateBack]
                  have postAgreement := Solidity.Yul.LocalBoolControl.source_agrees step glob frame fuel (finalLocals,final.2)
                  cases postRun : (Solidity.Source.evalE glob frame fuel post).run (finalLocals,final.2) with
                  | mk result after =>
                    rcases after with ⟨afterLocals,afterWorld⟩
                    rw [postRun] at postAgreement
                    cases result with
                    | error halt =>
                      change Solidity.Yul.LocalBoolControl.eval step fuel
                        (Solidity.Yul.LocalState.ofClean (finalLocals,final.2)) =
                        (.error halt,Solidity.Yul.LocalState.ofClean (afterLocals,afterWorld)) at postAgreement
                      have subPost : (Solidity.Source.EM.sub (Γ := []) finalLocals
                        (Solidity.Source.evalE glob frame fuel post)).run (Solidity.Source.L0 env,final.2) =
                        (.error halt,(Solidity.Source.L0 env,afterWorld)) := by
                        have actualRun : Solidity.Source.evalE (plan := none) (calldataKnown := true) glob frame fuel post (finalLocals,final.2) =
                          (.error halt,(afterLocals,afterWorld)) := postRun
                        simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
                      rw [postAgreement,Solidity.Source.Hoare.run_bind]
                      dsimp only [Solidity.Yul.LocalState.ofClean]
                      rw [subPost]
                      rfl
                    | ok value =>
                      cases value with
                      | val value =>
                        cases value with
                        | bool flag =>
                          change Solidity.Yul.LocalBoolControl.eval step fuel
                            (Solidity.Yul.LocalState.ofClean (finalLocals,final.2)) =
                            (.ok (.clean (.bool flag)),Solidity.Yul.LocalState.ofClean (afterLocals,afterWorld)) at postAgreement
                          have subPost : (Solidity.Source.EM.sub (Γ := []) finalLocals
                            (Solidity.Source.evalE glob frame fuel post)).run (Solidity.Source.L0 env,final.2) =
                            (.ok (.val (.bool flag),afterLocals),(Solidity.Source.L0 env,afterWorld)) := by
                            have actualRun : Solidity.Source.evalE (plan := none) (calldataKnown := true) glob frame fuel post (finalLocals,final.2) =
                              (.ok (.val (.bool flag)),(afterLocals,afterWorld)) := postRun
                            simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
                          rw [postAgreement,Solidity.Source.Hoare.run_bind]
                          dsimp only [Solidity.Yul.LocalState.ofClean]
                          rw [subPost]
                          exact ih afterLocals afterWorld
                        | memRef impossible _ => cases impossible
                        | storRef impossible _ => cases impossible
                        | cdRef impossible _ => cases impossible
          | memRef impossible _ => cases impossible
          | storRef impossible _ => cases impossible
          | cdRef impossible _ => cases impossible


end Solidity.Yul.LocalBoolPostIter
