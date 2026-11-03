import Solidity.Yul.LocalBoolItemScope

/-! Actual unchecked item scope followed by ordinary certified Boolean items. -/
namespace Solidity.Yul.LocalBoolUnchecked
def run {env returns modifier l types middle out inner rest}
    (inside : LocalBoolItems.Supported env returns modifier ⟨l,true⟩
      (types := types) (out := middle) inner)
    (tail : LocalBoolItems.Supported env returns modifier ⟨l,false⟩
      (types := types) (out := out) rest)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env out :=
  match fuel with
  | 0 => .halted .timeout state
  | fuel+1 =>
    LocalBoolItems.Result.casesOn (motive := fun _ => LocalBoolItems.Result env out)
      (LocalBoolItemScope.close inside (LocalBoolItems.run inside fuel state))
      (fun next => LocalBoolItems.run tail fuel next)
      (fun {_reached} halt next => .halted halt next)
/-- Concrete unchecked item composition, from completely clean input. -/
theorem source_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l : Bool) (types middle out : Solidity.Source.RCtx)
 (inner : Solidity.Source.RItems env returns modifier ⟨l,true⟩ types middle)
 (inside : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨l,true⟩ inner)
 (rest : Solidity.Source.RItems env returns modifier ⟨l,false⟩ types out)
 (tail : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨l,false⟩ rest)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalBoolUnchecked.run inside tail fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execItems glob frame fuel nps ph (.unchecked inner rest) locals).run
   (Solidity.Source.L0 env,world)) := by

  intro env returns modifier l types middle out inner inside rest tail glob frame fuel nps ph locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have innerAgreement := Solidity.Yul.LocalBoolItems.source_agrees env returns modifier ⟨l,true⟩
      types middle inner inside glob {frame with checked := false} fuel nps ph locals world
    rw [Solidity.Yul.LocalBoolUnchecked.run]
    cases innerRun : Solidity.Yul.LocalBoolItems.run inside fuel
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
        let restored := Solidity.Yul.LocalBoolItemScope.suffix env returns modifier ⟨l,true⟩
          types middle inner inside ▸ finalLocals.drop (middle.length - types.length)
        have restoredClean := Solidity.Yul.LocalBoolItemScope.restore_project env returns modifier ⟨l,true⟩
          types middle inner inside final finalLocals decoded
        have rebuilt := Solidity.Yul.LocalBoolItemScope.values_inverse env types
          (Solidity.Yul.LocalBoolItemScope.restore inside final).1 restored restoredClean
        have stateBack : Solidity.Yul.LocalState.ofClean (restored,final.2) =
            Solidity.Yul.LocalBoolItemScope.restore inside final := by
          apply Prod.ext
          · exact rebuilt
          · rfl
        rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,child]
        dsimp only []
        rw [Solidity.Yul.LocalBoolItemScope.source_restore env returns modifier ⟨l,true⟩
          types middle inner inside finalLocals]
        simp only [Solidity.Source.EM.lift,pure_bind]
        change Solidity.Yul.LocalBoolItems.project types
            (Solidity.Yul.LocalBoolItems.run tail fuel (Solidity.Yul.LocalBoolItemScope.restore inside final)) =
          some ((Solidity.Source.execItems glob frame fuel nps ph rest restored).run
            (Solidity.Source.L0 env,final.2))
        rw [← stateBack]
        exact Solidity.Yul.LocalBoolItems.source_agrees env returns modifier ⟨l,false⟩
          types out rest tail glob frame fuel nps ph restored final.2

def blockRun {env returns modifier l types middle out inner rest}
    (inside : LocalBoolItems.Supported env returns modifier ⟨l,true⟩
      (types := types) (out := middle) inner)
    (tail : LocalBoolItems.Supported env returns modifier ⟨l,false⟩
      (types := types) (out := out) rest)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env types :=
  match fuel with
  | 0 => .halted .timeout state
  | fuel+1 => LocalBoolItemScope.close tail (run inside tail fuel state)

/-- Concrete enclosing Source block; successful tail declarations close, halts retain reached context. -/
theorem block_source_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l : Bool) (types middle out : Solidity.Source.RCtx)
 (inner : Solidity.Source.RItems env returns modifier ⟨l,true⟩ types middle)
 (inside : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨l,true⟩ inner)
 (rest : Solidity.Source.RItems env returns modifier ⟨l,false⟩ types out)
 (tail : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨l,false⟩ rest)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalBoolUnchecked.blockRun inside tail fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph (.block (.unchecked inner rest)) locals).run
   (Solidity.Source.L0 env,world)) := by

  intro env returns modifier l types middle out inner inside rest tail glob frame fuel nps ph locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have child := Solidity.Yul.LocalBoolUnchecked.source_agrees env returns modifier l
      types middle out inner inside rest tail glob frame fuel nps ph locals world
    cases actual : Solidity.Yul.LocalBoolUnchecked.run inside tail fuel
      (Solidity.Yul.LocalState.ofClean (locals,world)) with
    | halted halt next =>
      rw [actual] at child
      change some ((Except.error halt : Solidity.Source.R (Solidity.Source.Out env.layout types out)),
        (Solidity.Source.L0 env,next.2)) = some _ at child
      have sourceChild := (Option.some.inj child).symm
      simp only [Solidity.Yul.LocalBoolUnchecked.blockRun,actual,Solidity.Yul.LocalBoolItemScope.close,
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
        have restored := Solidity.Yul.LocalBoolItemScope.restore_project env returns modifier ⟨l,false⟩
          types out rest tail next cleanLocals decoded
        have sourceRestore := Solidity.Yul.LocalBoolItemScope.source_restore env returns modifier ⟨l,false⟩
          types out rest tail cleanLocals
        simp only [Solidity.Yul.LocalBoolUnchecked.blockRun,actual,Solidity.Yul.LocalBoolItemScope.close,
          Solidity.Yul.LocalBoolItems.project,restored,Option.map_some]
        rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sourceChild]
        dsimp only []
        rw [Solidity.Source.Out.close,sourceRestore] <;> rfl


end Solidity.Yul.LocalBoolUnchecked

