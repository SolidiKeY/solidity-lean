import Solidity.Yul.LocalItemWorld

/-! Fuelled iteration of an actual Source Boolean condition and certified item scope.
Scope-local declarations are restored after each successful iteration. -/
namespace Solidity.Yul.LocalDefaultWhile

def run {env returns modifier types out condition u items}
    (test : LocalBoolControl.Supported env types condition)
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
        LocalBoolItems.Result.casesOn
          (motive := fun _ => LocalBoolItems.Result env types)
          (LocalDefaultItems.blockRun body fuel actual.2)
          (fun next => run test body fuel next)
          (fun {_reached} halt next => .halted halt next)
      else .normal actual.2


theorem source_agrees :  ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (l u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (branch : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalDefaultWhile.run test branch fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
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
        simp only [Solidity.Yul.LocalDefaultWhile.run,expression,Solidity.Yul.LocalBoolItems.project]
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
              rw [Solidity.Yul.LocalDefaultWhile.run,expression]
              simp only [Solidity.Yul.LocalBoolControl.truth_clean,
                Solidity.Yul.LocalBoolItems.project,Solidity.Yul.LocalState.ofClean,
                Solidity.Yul.LocalValues.clean_ofClean,Option.map_some,Bool.false_eq_true,if_false]
              rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub] <;> rfl
            | true =>
              simp only [Solidity.Yul.LocalDefaultWhile.run,expression,Solidity.Yul.LocalBoolControl.truth_clean]
              rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sub]
              dsimp only []
              rw [Solidity.Source.Hoare.run_bind]
              have getTrue : (Solidity.Source.getV (E := env) (Γ := [])
                  (Solidity.Source.RVal.val (Solidity.Source.Val.bool true))).run
                  (Solidity.Source.L0 env,nextWorld) =
                  (.ok (.bool true),(Solidity.Source.L0 env,nextWorld)) := by rfl
              rw [getTrue]
              dsimp only []
              have scopeAgreement := Solidity.Yul.LocalDefaultItems.block_source_agrees env returns modifier ⟨true,u⟩
                types out items branch glob frame fuel nps ph nextLocals nextWorld
              cases branchRun : Solidity.Yul.LocalDefaultItems.blockRun branch fuel
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
                    (Solidity.Yul.LocalDefaultWhile.run test branch fuel final) =
                    some ((Solidity.Source.execS glob frame fuel nps ph
                      (.whileLoop (l := l) condition (.block items)) finalLocals).run
                      (Solidity.Source.L0 env,final.2))
                  rw [← stateBack]
                  exact ih finalLocals final.2
          | memRef impossible _ => cases impossible
          | storRef impossible _ => cases impossible
          | cdRef impossible _ => cases impossible




theorem no_normal :  ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state next : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultWhile.run (.base (.literal true)) body fuel state ≠ .normal next := by


  intro env returns modifier u types out items body fuel
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
        (fun after => Solidity.Yul.LocalDefaultWhile.run (.base (.literal true)) body (fuel+1) after)
        (fun {_reached} halt after => .halted halt after) ≠ .normal next
      cases actual : Solidity.Yul.LocalDefaultItems.blockRun body (fuel+1) state with
      | normal after => exact ih after next
      | halted halt after =>
        intro bad
        cases bad




theorem world :  ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (branch : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalItemWorld.world (Solidity.Yul.LocalDefaultWhile.run test branch fuel state) = state.2 := by

  intro env returns modifier u types out condition test items branch fuel state
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    have same := Solidity.Yul.LocalBoolControl.world test fuel state
    cases actual : Solidity.Yul.LocalBoolControl.eval test fuel state with
    | mk result next =>
      rw [actual] at same
      rw [Solidity.Yul.LocalDefaultWhile.run,actual]
      cases result with
      | error halt => exact same
      | ok value =>
        cases choice : Solidity.Yul.LocalBoolControl.truth value with
        | false =>
          simp only [choice,Bool.false_eq_true,if_false]
          exact same
        | true =>
          simp only [choice,if_true]
          have preserved := Solidity.Yul.LocalItemWorld.default_block env returns modifier ⟨true,u⟩
            types out items branch fuel next
          cases step : Solidity.Yul.LocalDefaultItems.blockRun branch fuel next with
          | normal after =>
            rw [step] at preserved
            exact (ih after).trans (preserved.trans same)
          | halted halt after =>
            rw [step] at preserved
            exact preserved.trans same

/-- Excludes every finite normal Source outcome for the actual constant-true supported loop. -/
theorem source_no_normal :  ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l u : Bool) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals next : Solidity.Source.Locals env.layout types) (world finalWorld : Solidity.Source.St env),
 (Solidity.Source.execS glob frame fuel nps ph
   (.whileLoop (l := l) (.bool true) (.block items)) locals).run
   (Solidity.Source.L0 env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 env,finalWorld)) := by


  intro env returns modifier l u types out items body glob frame fuel nps ph locals next world finalWorld
  have agreement := Solidity.Yul.LocalDefaultWhile.source_agrees env returns modifier l u types out
    (.bool true) (.base (.literal true)) items body glob frame fuel nps ph locals world
  cases actual : Solidity.Yul.LocalDefaultWhile.run (.base (.literal true)) body fuel
    (Solidity.Yul.LocalState.ofClean (locals,world)) with
  | normal after =>
    exact False.elim (Solidity.Yul.LocalDefaultWhile.no_normal env returns modifier u types out
      items body fuel (Solidity.Yul.LocalState.ofClean (locals,world)) after actual)
  | halted halt after =>
    rw [actual] at agreement
    change some ((Except.error halt : Solidity.Source.R (Solidity.Source.Out env.layout types types)),
      (Solidity.Source.L0 env,after.2)) = some _ at agreement
    intro bad
    rw [bad] at agreement
    cases agreement



end Solidity.Yul.LocalDefaultWhile
