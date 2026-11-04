import Solidity.Yul.LocalBoolWhile
import Solidity.Yul.RawSourceForIter
import Solidity.Yul.RawLocalScope

/-! Concrete for statements with a Boolean initializer, scoped item body and no post. -/
namespace Solidity.Yul.LocalBoolFor

def close {env types} (result : LocalBoolItems.Result env (.bool :: types)) :
    LocalBoolItems.Result env types :=
  LocalBoolItems.Result.casesOn (motive := fun _ => LocalBoolItems.Result env types)
    result (fun next => .normal (next.1.2,next.2))
    (fun {_reached} halt next => .halted halt next)

def run {env returns modifier types out init condition u items}
    (initializer : LocalBoolControl.Supported env types init)
    (test : LocalBoolControl.Supported env (.bool :: types) condition)
    (body : LocalBoolItems.Supported env returns modifier ⟨true,u⟩
      (types := .bool :: types) (out := out) items)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env types :=
  match fuel with
  | 0 => .halted .timeout state
  | fuel+1 =>
    LocalBoolInitialization.Result.casesOn (motive := fun _ => LocalBoolItems.Result env types)
      (LocalBoolInitialization.run initializer fuel state)
      (fun next => close (LocalBoolWhile.run test body fuel next))
      (fun halt next => .halted halt next)

/-- Actual Source forLoop agreement for Boolean initialization and scoped body, no post.
Requires a completely clean input frame; no dirty Source/compiler adequacy is asserted. -/
theorem source_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (condition : Solidity.Source.RExpr env (.bool :: types) .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalBoolFor.run initializer test body fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph
   (.forLoop (l := l) (.declInit (τ := .bool) init (by rfl)) (.some condition) .none (.block items))
   locals).run (Solidity.Source.L0 env,world)) := by

  intro env returns modifier l u types out init initializer condition test items body glob frame fuel nps ph locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have declaration := Solidity.Yul.LocalBoolInitialization.source_agrees env types init initializer
      glob frame fuel nps ph returns modifier ⟨true,u⟩ locals world
    rw [Solidity.Yul.LocalBoolFor.run]
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
        rw [Solidity.Yul.RawSourceForIter.source_while]
        rw [← stateBack]
        have iteration := Solidity.Yul.LocalBoolWhile.source_agrees env returns modifier true u
          (.bool :: types) out condition test items body glob frame fuel nps ph initialLocals initial.2
        cases loopRun : Solidity.Yul.LocalBoolWhile.run test body fuel
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


end Solidity.Yul.LocalBoolFor
