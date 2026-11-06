import Solidity.Yul.LocalBoolFor
import Solidity.Yul.LocalBoolPostIter

/-! Actual for statements with certified Boolean initializer, guard/post and item body. -/
namespace Solidity.Yul.LocalBoolForPost
def run {env returns modifier types out init condition post u items}
    (initializer : LocalBoolControl.Supported env types init)
    (test : LocalBoolControl.Supported env (.bool :: types) condition)
    (step : LocalBoolControl.Supported env (.bool :: types) post)
    (body : LocalBoolItems.Supported env returns modifier ⟨true,u⟩
      (types := .bool :: types) (out := out) items)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env types :=
  match fuel with
  | 0 => .halted .timeout state
  | fuel+1 =>
    LocalBoolInitialization.Result.casesOn (motive := fun _ => LocalBoolItems.Result env types)
      (LocalBoolInitialization.run initializer fuel state)
      (fun next => LocalBoolFor.close (LocalBoolPostIter.run test step body fuel next))
      (fun halt next => .halted halt next)
/-- Concrete full for statement with present Boolean guard/post and certified scopes.
Requires completely clean input; no dirty Source/compiler adequacy. -/
theorem source_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (condition : Solidity.Source.RExpr env (.bool :: types) .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) condition)
 (post : Solidity.Source.RExpr env (.bool :: types) .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalBoolForPost.run initializer test step body fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph
   (.forLoop (l := l) (.declInit (τ := .bool) init (by rfl)) (.some condition) (.some post) (.block items))
   locals).run (Solidity.Source.L0 env,world)) := by


  intro env returns modifier l u types out init initializer condition test post step items body glob frame fuel nps ph locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have declaration := Solidity.Yul.LocalBoolInitialization.source_agrees env types init initializer
      glob frame fuel nps ph returns modifier ⟨true,u⟩ locals world
    rw [Solidity.Yul.LocalBoolForPost.run]
    cases initialRun : Solidity.Yul.LocalBoolInitialization.run initializer fuel
      (Solidity.Yul.LocalState.ofClean (locals,world)) with
    | halted halt final =>
      rw [initialRun] at declaration
      change some ((Except.error halt : Solidity.Source.R
        (Solidity.Source.Out env.layout types (.bool :: types))),(Solidity.Source.L0 env,final.2)) = some _ at declaration
      have child := (Option.some.inj declaration).symm
      rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,child]
      rfl
    | normal initial =>
      rw [initialRun] at declaration
      cases decoded : Solidity.Yul.LocalValues.clean? (.bool :: types) initial.1 with
      | none =>
        simp only [Solidity.Yul.LocalBoolInitialization.project,decoded,Option.map_none] at declaration
        cases declaration
      | some initialLocals =>
        simp only [Solidity.Yul.LocalBoolInitialization.project,decoded,Option.map_some] at declaration
        have child := (Option.some.inj declaration).symm
        have rebuilt := Solidity.Yul.LocalBoolItemScope.values_inverse env (.bool :: types)
          initial.1 initialLocals decoded
        have stateBack : Solidity.Yul.LocalState.ofClean (initialLocals,initial.2) = initial := by
          cases initial
          simp only [Solidity.Yul.LocalState.ofClean]
          rw [rebuilt]
        rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,child]
        dsimp only []
        rw [← stateBack]
        have iteration := Solidity.Yul.LocalBoolPostIter.source_agrees env returns modifier u
          (.bool :: types) out condition test post step items body glob frame fuel nps ph initialLocals initial.2
        cases loopRun : Solidity.Yul.LocalBoolPostIter.run test step body fuel
          (Solidity.Yul.LocalState.ofClean (initialLocals,initial.2)) with
        | halted halt final =>
          rw [loopRun] at iteration
          change some ((Except.error halt : Solidity.Source.R
            (Solidity.Source.Out env.layout (.bool :: types) (.bool :: types))),
              (Solidity.Source.L0 env,final.2)) = some _ at iteration
          have iterChild := (Option.some.inj iteration).symm
          rw [Solidity.Source.Hoare.run_bind]
          dsimp only [Solidity.Yul.LocalState.ofClean]
          rw [iterChild]
          rfl
        | normal final =>
          rw [loopRun] at iteration
          cases finalDecoded : Solidity.Yul.LocalValues.clean? (.bool :: types) final.1 with
          | none =>
            simp only [Solidity.Yul.LocalBoolItems.project,finalDecoded,Option.map_none] at iteration
            cases iteration
          | some finalLocals =>
            simp only [Solidity.Yul.LocalBoolItems.project,finalDecoded,Option.map_some] at iteration
            have iterChild := (Option.some.inj iteration).symm
            have rebuiltFinal := Solidity.Yul.LocalBoolItemScope.values_inverse env (.bool :: types)
              final.1 finalLocals finalDecoded
            rw [Solidity.Source.Hoare.run_bind]
            dsimp only [Solidity.Yul.LocalState.ofClean]
            rw [iterChild]
            cases finalLocals with
            | cons value rest =>
              dsimp only []
              rw [Solidity.Yul.RawLocalScope.restore_cons]
              rw [Solidity.Yul.LocalBoolFor.close]
              simp only [Solidity.Yul.LocalBoolItems.project]
              rw [← rebuiltFinal]
              change (Solidity.Yul.LocalValues.clean? types (Solidity.Yul.LocalValues.ofClean (env := env) rest)).map
                (fun ls => ((Except.ok (Solidity.Source.Out.normal ls) :
                  Solidity.Source.R (Solidity.Source.Out env.layout types types)),(Solidity.Source.L0 env,final.2))) = _
              rw [Solidity.Yul.LocalValues.clean_ofClean]
              rfl


end Solidity.Yul.LocalBoolForPost
