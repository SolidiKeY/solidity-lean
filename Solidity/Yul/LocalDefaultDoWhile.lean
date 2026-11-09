import Solidity.Yul.LocalDefaultWhile

/-! Actual Source do/while with a certified context-growing Boolean item scope. -/
namespace Solidity.Yul.LocalDefaultDoWhile
def run {env returns modifier types out condition u items}
    (test : LocalBoolControl.Supported env types condition)
    (body : LocalDefaultItems.Supported env returns modifier ⟨true,u⟩
      (types := types) (out := out) items) :
    Nat → LocalState env types → LocalBoolItems.Result env types
  | 0, state => .halted .timeout state
  | fuel+1, state =>
    LocalBoolItems.Result.casesOn (motive := fun _ => LocalBoolItems.Result env types)
      (LocalDefaultItems.blockRun body fuel state)
      (fun next =>
        let actual := LocalBoolControl.eval test fuel next
        match actual.1 with
        | .error halt => .halted halt actual.2
        | .ok value =>
          if LocalBoolControl.truth value then run test body fuel actual.2
          else .normal actual.2)
      (fun {_reached} halt next => .halted halt next)

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
   (Solidity.Yul.LocalDefaultDoWhile.run test branch fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph (.doWhile (l := l) (.block items) condition) locals).run
   (Solidity.Source.L0 env,world)) := by


  intro env returns modifier l u types out condition test items branch glob frame fuel nps ph locals world
  induction fuel generalizing locals world with
  | zero => rfl
  | succ fuel ih =>
    have scopeAgreement := Solidity.Yul.LocalDefaultItems.block_source_agrees env returns modifier ⟨true,u⟩
      types out items branch glob frame fuel nps ph locals world
    rw [Solidity.Yul.LocalDefaultDoWhile.run]
    cases branchRun : Solidity.Yul.LocalDefaultItems.blockRun branch fuel
      (Solidity.Yul.LocalState.ofClean (locals,world)) with
    | halted halt final =>
      rw [branchRun] at scopeAgreement
      change some ((Except.error halt : Solidity.Source.R
        (Solidity.Source.Out env.layout types types)),(Solidity.Source.L0 env,final.2)) = some _ at scopeAgreement
      have child := (Option.some.inj scopeAgreement).symm
      rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,child]
      rfl
    | normal final =>
      rw [branchRun] at scopeAgreement
      cases decoded : Solidity.Yul.LocalValues.clean? types final.1 with
      | none =>
        simp only [Solidity.Yul.LocalBoolItems.project,decoded,Option.map_none] at scopeAgreement
        cases scopeAgreement
      | some afterLocals =>
        simp only [Solidity.Yul.LocalBoolItems.project,decoded,Option.map_some] at scopeAgreement
        have child := (Option.some.inj scopeAgreement).symm
        have rebuilt := Solidity.Yul.LocalBoolItemScope.values_inverse env types final.1 afterLocals decoded
        have stateBack : Solidity.Yul.LocalState.ofClean (afterLocals,final.2) = final := by
          cases final
          simp only [Solidity.Yul.LocalState.ofClean]
          rw [rebuilt]
        rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,child]
        dsimp only []
        rw [Solidity.Yul.RawSequence.restore_self]
        have liftSelf : (Solidity.Source.EM.lift (E := env) (Γ := [])
            (Except.ok afterLocals : Solidity.Source.R (Solidity.Source.Locals env.layout types))).run
            (Solidity.Source.L0 env,final.2) =
            (.ok afterLocals,(Solidity.Source.L0 env,final.2)) := by rfl
        rw [Solidity.Source.Hoare.run_bind,liftSelf]
        dsimp only []
        rw [← stateBack]
        have expression := Solidity.Yul.LocalBoolControl.source_agrees test glob frame fuel (afterLocals,final.2)
        cases actual : (Solidity.Source.evalE glob frame fuel condition).run (afterLocals,final.2) with
        | mk result next =>
          rcases next with ⟨nextLocals,nextWorld⟩
          rw [actual] at expression
          cases result with
          | error halt =>
            change Solidity.Yul.LocalBoolControl.eval test fuel
                (Solidity.Yul.LocalState.ofClean (afterLocals,final.2)) =
                (.error halt,Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld)) at expression
            have sub : (Solidity.Source.EM.sub (Γ := []) afterLocals
                (Solidity.Source.evalE glob frame fuel condition)).run (Solidity.Source.L0 env,final.2) =
                (.error halt,(Solidity.Source.L0 env,nextWorld)) := by
              have actualRun : Solidity.Source.evalE (plan := none) (calldataKnown := true) glob frame fuel condition (afterLocals,final.2) =
                (.error halt,(nextLocals,nextWorld)) := actual
              simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
            rw [expression,Solidity.Source.Hoare.run_bind]
            dsimp only [Solidity.Yul.LocalState.ofClean]
            rw [sub]
            rfl
          | ok value =>
            cases value with
            | val value =>
              cases value with
              | bool value =>
                change Solidity.Yul.LocalBoolControl.eval test fuel
                  (Solidity.Yul.LocalState.ofClean (afterLocals,final.2)) =
                  (.ok (.clean (.bool value)),Solidity.Yul.LocalState.ofClean (nextLocals,nextWorld)) at expression
                have sub : (Solidity.Source.EM.sub (Γ := []) afterLocals
                    (Solidity.Source.evalE glob frame fuel condition)).run (Solidity.Source.L0 env,final.2) =
                    (.ok (.val (.bool value),nextLocals),(Solidity.Source.L0 env,nextWorld)) := by
                  have actualRun : Solidity.Source.evalE (plan := none) (calldataKnown := true) glob frame fuel condition (afterLocals,final.2) =
                    (.ok (.val (.bool value)),(nextLocals,nextWorld)) := actual
                  simp only [Solidity.Source.EM.sub,ExceptT.run,ExceptT.mk,actualRun]
                rw [expression,Solidity.Source.Hoare.run_bind]
                dsimp only [Solidity.Yul.LocalState.ofClean]
                rw [sub]
                cases value with
                | false =>
                  simp only [Solidity.Yul.LocalBoolControl.truth_clean,Bool.false_eq_true,if_false,
                    Solidity.Yul.LocalBoolItems.project,
                    Solidity.Yul.LocalValues.clean_ofClean,Option.map_some]
                  rfl
                | true =>
                  simp only [Solidity.Yul.LocalBoolControl.truth_clean,if_true]
                  rw [Solidity.Source.Hoare.run_bind]
                  have getTrue : (Solidity.Source.getV (E := env) (Γ := [])
                    (Solidity.Source.RVal.val (Solidity.Source.Val.bool true))).run
                    (Solidity.Source.L0 env,nextWorld) =
                    (.ok (.bool true),(Solidity.Source.L0 env,nextWorld)) := by rfl
                  rw [getTrue]
                  exact ih nextLocals nextWorld
              | memRef impossible _ => cases impossible
              | storRef impossible _ => cases impossible
              | cdRef impossible _ => cases impossible




theorem no_normal :  ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state next : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultDoWhile.run (.base (.literal true)) body fuel state ≠ .normal next := by


  intro env returns modifier u types out items body fuel
  induction fuel with
  | zero =>
    intro state next bad
    cases bad
  | succ fuel ih =>
    intro state next
    rw [Solidity.Yul.LocalDefaultDoWhile.run]
    cases actual : Solidity.Yul.LocalDefaultItems.blockRun body fuel state with
    | halted halt after =>
      intro bad
      cases bad
    | normal after =>
      cases fuel with
      | zero =>
        intro bad
        cases bad
      | succ fuel =>
        change Solidity.Yul.LocalDefaultDoWhile.run (.base (.literal true)) body (fuel+1) after ≠ .normal next
        exact ih after next




theorem world :  ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (branch : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalItemWorld.world (Solidity.Yul.LocalDefaultDoWhile.run test branch fuel state) = state.2 := by

  intro env returns modifier u types out condition test items branch fuel state
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    have kept := Solidity.Yul.LocalItemWorld.default_block env returns modifier ⟨true,u⟩
      types out items branch fuel state
    rw [Solidity.Yul.LocalDefaultDoWhile.run]
    cases step : Solidity.Yul.LocalDefaultItems.blockRun branch fuel state with
    | halted halt after =>
      rw [step] at kept
      exact kept
    | normal after =>
      rw [step] at kept
      dsimp only []
      have same := Solidity.Yul.LocalBoolControl.world test fuel after
      cases actual : Solidity.Yul.LocalBoolControl.eval test fuel after with
      | mk result next =>
        rw [actual] at same
        cases result with
        | error halt => exact same.trans kept
        | ok value =>
          cases choice : Solidity.Yul.LocalBoolControl.truth value with
          | false =>
            simp only [choice,Bool.false_eq_true,if_false]
            exact same.trans kept
          | true =>
            simp only [choice,if_true]
            exact (ih next).trans (same.trans kept)

theorem source_no_normal :  ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l u : Bool) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals next : Solidity.Source.Locals env.layout types) (world finalWorld : Solidity.Source.St env),
 (Solidity.Source.execS glob frame fuel nps ph
   (.doWhile (l := l) (.block items) (.bool true)) locals).run
   (Solidity.Source.L0 env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 env,finalWorld)) := by



  intro env returns modifier l u types out items body glob frame fuel nps ph locals next world finalWorld
  have agreement := Solidity.Yul.LocalDefaultDoWhile.source_agrees env returns modifier l u types out
    (.bool true) (.base (.literal true)) items body glob frame fuel nps ph locals world
  cases actual : Solidity.Yul.LocalDefaultDoWhile.run (.base (.literal true)) body fuel
    (Solidity.Yul.LocalState.ofClean (locals,world)) with
  | normal after =>
    exact False.elim (Solidity.Yul.LocalDefaultDoWhile.no_normal env returns modifier u types out
      items body fuel (Solidity.Yul.LocalState.ofClean (locals,world)) after actual)
  | halted halt after =>
    rw [actual] at agreement
    change some ((Except.error halt : Solidity.Source.R (Solidity.Source.Out env.layout types types)),
      (Solidity.Source.L0 env,after.2)) = some _ at agreement
    intro bad
    rw [bad] at agreement
    cases agreement



end Solidity.Yul.LocalDefaultDoWhile
