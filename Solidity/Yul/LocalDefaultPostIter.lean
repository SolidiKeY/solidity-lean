import Solidity.Yul.LocalDefaultWhile

/-! Actual for iterations with certified Boolean guard/post and a default-declaration scope. -/
namespace Solidity.Yul.LocalDefaultPostIter

def run {env returns modifier types out condition post u items}
    (test : LocalBoolControl.Supported env types condition)
    (step : LocalBoolControl.Supported env types post)
    (body : LocalDefaultItems.Supported env returns modifier ⟨true,u⟩
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
          (LocalDefaultItems.blockRun body fuel actual.2)
          (fun next =>
            let updated := LocalBoolControl.eval step fuel next
            match updated.1 with
            | .error halt => .halted halt updated.2
            | .ok _ => run test step body fuel updated.2)
          (fun {_reached} halt next => .halted halt next)
      else .normal actual.2

theorem source_agrees :  ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (post : Solidity.Source.RExpr env types .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env types post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (branch : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalDefaultPostIter.run test step branch fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
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
        simp only [Solidity.Yul.LocalDefaultPostIter.run,expression,Solidity.Yul.LocalBoolItems.project]
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
              rw [Solidity.Yul.LocalDefaultPostIter.run,expression]
              simp only [Solidity.Yul.LocalBoolControl.truth_clean,
                Solidity.Yul.LocalBoolItems.project,Solidity.Yul.LocalState.ofClean,
                Solidity.Yul.LocalValues.clean_ofClean,Option.map_some,Bool.false_eq_true,if_false]
              rw [Solidity.Source.forIter]
              simp only [pure_bind]
              rw [Solidity.Source.Hoare.run_bind,sub] <;> rfl
            | true =>
              simp only [Solidity.Yul.LocalDefaultPostIter.run,expression,Solidity.Yul.LocalBoolControl.truth_clean]
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
              have scopeAgreement := Solidity.Yul.LocalDefaultItems.block_source_agrees env returns modifier ⟨true,u⟩
                types out items branch glob frame fuel nps ph nextLocals nextWorld
              cases branchRun : Solidity.Yul.LocalDefaultItems.blockRun branch fuel
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




theorem no_normal : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (post : Solidity.Source.RExpr env types .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env types post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state next : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultPostIter.run (.base (.literal true)) step body fuel state ≠ .normal next := by

  intro env returns modifier u types out post step items body fuel
  induction fuel with
  | zero =>
    intro state next bad
    cases bad
  | succ fuel ih =>
    intro state next
    cases fuel with
    | zero =>
      intro bad
      cases bad
    | succ fuel =>
      change Solidity.Yul.LocalBoolItems.Result.casesOn
        (motive := fun _ => Solidity.Yul.LocalBoolItems.Result env types)
        (Solidity.Yul.LocalDefaultItems.blockRun body (fuel+1) state)
        (fun after =>
          let updated := Solidity.Yul.LocalBoolControl.eval step (fuel+1) after
          match updated.1 with
          | .error halt => .halted halt updated.2
          | .ok _ => Solidity.Yul.LocalDefaultPostIter.run (.base (.literal true)) step body (fuel+1) updated.2)
        (fun {_reached} halt after => .halted halt after) ≠ .normal next
      cases bodyRun : Solidity.Yul.LocalDefaultItems.blockRun body (fuel+1) state with
      | halted halt after =>
        intro bad
        cases bad
      | normal after =>
        dsimp only []
        cases postRun : Solidity.Yul.LocalBoolControl.eval step (fuel+1) after with
        | mk result final =>
          cases result with
          | error halt =>
            intro bad
            cases bad
          | ok _value => exact ih final next

theorem world :  ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (post : Solidity.Source.RExpr env types .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env types post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (branch : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalItemWorld.world (Solidity.Yul.LocalDefaultPostIter.run test step branch fuel state) = state.2 := by

  intro env returns modifier u types out condition test post step items branch fuel state
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    have guardWorld := Solidity.Yul.LocalBoolControl.world test fuel state
    cases actual : Solidity.Yul.LocalBoolControl.eval test fuel state with
    | mk result next =>
      rw [actual] at guardWorld
      rw [Solidity.Yul.LocalDefaultPostIter.run,actual]
      cases result with
      | error halt => exact guardWorld
      | ok value =>
        cases choice : Solidity.Yul.LocalBoolControl.truth value with
        | false =>
          simp only [choice,Bool.false_eq_true,if_false]
          exact guardWorld
        | true =>
          simp only [choice,if_true]
          have bodyWorld := Solidity.Yul.LocalItemWorld.default_block env returns modifier ⟨true,u⟩
            types out items branch fuel next
          cases bodyRun : Solidity.Yul.LocalDefaultItems.blockRun branch fuel next with
          | halted halt after =>
            rw [bodyRun] at bodyWorld
            exact bodyWorld.trans guardWorld
          | normal after =>
            rw [bodyRun] at bodyWorld
            dsimp only []
            have postWorld := Solidity.Yul.LocalBoolControl.world step fuel after
            cases postRun : Solidity.Yul.LocalBoolControl.eval step fuel after with
            | mk postResult final =>
              rw [postRun] at postWorld
              cases postResult with
              | error halt => exact postWorld.trans (bodyWorld.trans guardWorld)
              | ok _value => exact (ih final).trans (postWorld.trans (bodyWorld.trans guardWorld))

/-- No finite normal Source outcome for a constant guard, regardless of post truth value. -/
theorem source_no_normal : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (post : Solidity.Source.RExpr env types .bool)
 (_step : Solidity.Yul.LocalBoolControl.Supported env types post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (_body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals next : Solidity.Source.Locals env.layout types) (world finalWorld : Solidity.Source.St env),
 (Solidity.Source.forIter glob frame fuel nps ph (.some (.bool true)) (.some post) (.block items) locals).run
 (Solidity.Source.L0 env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 env,finalWorld)) := by

  intro env returns modifier u types out post step items body glob frame fuel nps ph locals next world finalWorld
  have agreement := Solidity.Yul.LocalDefaultPostIter.source_agrees env returns modifier u types out
    (.bool true) (.base (.literal true)) post step items body glob frame fuel nps ph locals world
  cases actual : Solidity.Yul.LocalDefaultPostIter.run (.base (.literal true)) step body fuel
    (Solidity.Yul.LocalState.ofClean (locals,world)) with
  | normal after =>
    exact False.elim (Solidity.Yul.LocalDefaultPostIter.no_normal env returns modifier u types out
      post step items body fuel (Solidity.Yul.LocalState.ofClean (locals,world)) after actual)
  | halted halt after =>
    rw [actual] at agreement
    change some ((Except.error halt : Solidity.Source.R (Solidity.Source.Out env.layout types types)),
      (Solidity.Source.L0 env,after.2)) = some _ at agreement
    intro bad
    rw [bad] at agreement
    cases agreement
end Solidity.Yul.LocalDefaultPostIter
