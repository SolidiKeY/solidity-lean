import Solidity.Yul.LocalDefaultItems

/-! Actual unchecked default-declaration scope followed by ordinary certified default items. -/
namespace Solidity.Yul.LocalDefaultUnchecked
def run {env returns modifier l types middle out inner rest}
    (inside : LocalDefaultItems.Supported env returns modifier ⟨l,true⟩
      (types := types) (out := middle) inner)
    (tail : LocalDefaultItems.Supported env returns modifier ⟨l,false⟩
      (types := types) (out := out) rest)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env out :=
  match fuel with
  | 0 => .halted .timeout state
  | fuel+1 =>
    LocalBoolItems.Result.casesOn (motive := fun _ => LocalBoolItems.Result env out)
      (LocalDefaultItems.close inside (LocalDefaultItems.run inside fuel state))
      (fun next => LocalDefaultItems.run tail fuel next)
      (fun {_reached} halt next => .halted halt next)
/-- Close the ordinary continuation as an enclosing block. -/

def blockRun {env returns modifier l types middle out inner rest}
    (inside : LocalDefaultItems.Supported env returns modifier ⟨l,true⟩
      (types := types) (out := middle) inner)
    (tail : LocalDefaultItems.Supported env returns modifier ⟨l,false⟩
      (types := types) (out := out) rest)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env types :=
  match fuel with
  | 0 => .halted .timeout state
  | fuel+1 => LocalDefaultItems.close tail (run inside tail fuel state)



theorem source_agrees :  ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l : Bool) (types middle out : Solidity.Source.RCtx)
 (inner : Solidity.Source.RItems env returns modifier ⟨l,true⟩ types middle)
 (inside : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,true⟩ inner)
 (rest : Solidity.Source.RItems env returns modifier ⟨l,false⟩ types out)
 (tail : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,false⟩ rest)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalDefaultUnchecked.run inside tail fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execItems glob frame fuel nps ph (.unchecked inner rest) locals).run
   (Solidity.Source.L0 env,world)) := by


  intro env returns modifier l types middle out inner inside rest tail glob frame fuel nps ph locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have innerAgreement := Solidity.Yul.LocalDefaultItems.source_agrees env returns modifier ⟨l,true⟩
      types middle inner inside glob {frame with checked := false} fuel nps ph locals world
    rw [Solidity.Yul.LocalDefaultUnchecked.run]
    cases innerRun : Solidity.Yul.LocalDefaultItems.run inside fuel
      (Solidity.Yul.LocalState.ofClean (locals,world)) with
    | halted halt final =>
      rw [innerRun] at innerAgreement
      change some ((Except.error halt : Solidity.Source.R
        (Solidity.Source.Out env.layout types middle)),(Solidity.Source.L0 env,final.2)) = some _ at innerAgreement
      have child := (Option.some.inj innerAgreement).symm
      rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,child]
      rfl
    | normal final =>
      rw [innerRun] at innerAgreement
      cases decoded : Solidity.Yul.LocalValues.clean? middle final.1 with
      | none =>
        simp only [Solidity.Yul.LocalBoolItems.project,decoded,Option.map_none] at innerAgreement
        cases innerAgreement
      | some finalLocals =>
        simp only [Solidity.Yul.LocalBoolItems.project,decoded,Option.map_some] at innerAgreement
        have child := (Option.some.inj innerAgreement).symm
        let restored := (Solidity.Yul.LocalDefaultItems.context env returns modifier ⟨l,true⟩
          types middle inner inside).2 ▸ finalLocals.drop (middle.length - types.length)
        have restoredClean := Solidity.Yul.LocalDefaultItems.restore_project env returns modifier ⟨l,true⟩
          types middle inner inside final finalLocals decoded
        have rebuilt := Solidity.Yul.LocalBoolItemScope.values_inverse env types
          (Solidity.Yul.LocalDefaultItems.restore inside final).1 restored restoredClean
        have stateBack : Solidity.Yul.LocalState.ofClean (restored,final.2) =
            Solidity.Yul.LocalDefaultItems.restore inside final := by
          apply Prod.ext
          · exact rebuilt
          · rfl
        rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,child]
        dsimp only []
        rw [Solidity.Yul.LocalDefaultItems.source_restore env returns modifier ⟨l,true⟩
          types middle inner inside finalLocals]
        simp only [Solidity.Source.EM.lift,pure_bind]
        change Solidity.Yul.LocalBoolItems.project types
            (Solidity.Yul.LocalDefaultItems.run tail fuel (Solidity.Yul.LocalDefaultItems.restore inside final)) =
          some ((Solidity.Source.execItems glob frame fuel nps ph rest restored).run
            (Solidity.Source.L0 env,final.2))
        rw [← stateBack]
        exact Solidity.Yul.LocalDefaultItems.source_agrees env returns modifier ⟨l,false⟩
          types out rest tail glob frame fuel nps ph restored final.2


/-- Concrete enclosing block agreement from clean input; failures retain their reached context. -/
theorem block_source_agrees :  ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l : Bool) (types middle out : Solidity.Source.RCtx)
 (inner : Solidity.Source.RItems env returns modifier ⟨l,true⟩ types middle)
 (inside : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,true⟩ inner)
 (rest : Solidity.Source.RItems env returns modifier ⟨l,false⟩ types out)
 (tail : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,false⟩ rest)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalDefaultUnchecked.blockRun inside tail fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph (.block (.unchecked inner rest)) locals).run
   (Solidity.Source.L0 env,world)) := by


  intro env returns modifier l types middle out inner inside rest tail glob frame fuel nps ph locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have child := Solidity.Yul.LocalDefaultUnchecked.source_agrees env returns modifier l
      types middle out inner inside rest tail glob frame fuel nps ph locals world
    cases actual : Solidity.Yul.LocalDefaultUnchecked.run inside tail fuel
      (Solidity.Yul.LocalState.ofClean (locals,world)) with
    | halted halt next =>
      rw [actual] at child
      change some ((Except.error halt : Solidity.Source.R (Solidity.Source.Out env.layout types out)),
        (Solidity.Source.L0 env,next.2)) = some _ at child
      have sourceChild := (Option.some.inj child).symm
      simp only [Solidity.Yul.LocalDefaultUnchecked.blockRun,actual,Solidity.Yul.LocalDefaultItems.close,
        Solidity.Yul.LocalBoolItems.project]
      rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sourceChild] <;> rfl
    | normal next =>
      rw [actual] at child
      cases decoded : Solidity.Yul.LocalValues.clean? out next.1 with
      | none =>
        simp only [Solidity.Yul.LocalBoolItems.project,decoded,Option.map_none] at child
        cases child
      | some cleanLocals =>
        simp only [Solidity.Yul.LocalBoolItems.project,decoded,Option.map_some] at child
        have sourceChild := (Option.some.inj child).symm
        have restored := Solidity.Yul.LocalDefaultItems.restore_project env returns modifier ⟨l,false⟩
          types out rest tail next cleanLocals decoded
        have sourceRestore := Solidity.Yul.LocalDefaultItems.source_restore env returns modifier ⟨l,false⟩
          types out rest tail cleanLocals
        simp only [Solidity.Yul.LocalDefaultUnchecked.blockRun,actual,Solidity.Yul.LocalDefaultItems.close,
          Solidity.Yul.LocalBoolItems.project,restored,Option.map_some]
        rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sourceChild]
        dsimp only []
        rw [Solidity.Source.Out.close,sourceRestore] <;> rfl



end Solidity.Yul.LocalDefaultUnchecked
