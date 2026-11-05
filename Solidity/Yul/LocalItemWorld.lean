import Solidity.Yul.LocalDefaultUnchecked

/-! World preservation for pure local item execution, including dirty inputs and partial halts.
This observes the existing Source world; it defines no physical or world-effect semantics. -/
namespace Solidity.Yul.LocalItemWorld

def world {env out} (result : LocalBoolItems.Result env out) : Solidity.Source.St env :=
  LocalBoolItems.Result.casesOn (motive := fun _ => Solidity.Source.St env) result
    (fun next => next.2) (fun {_reached} _ next => next.2)


/-- Pure Boolean items preserve the world on every raw input and every horizon. -/
theorem bool_run : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalItemWorld.world (Solidity.Yul.LocalBoolItems.run proof fuel state) = state.2 := by

  intro env returns modifier control types out items proof fuel state
  induction proof generalizing fuel with
  | nil =>
    cases fuel <;> rfl
  | @expression types out expr rest one tail ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
        have same := Solidity.Yul.LocalBoolControl.world one fuel state
        cases actual : Solidity.Yul.LocalBoolControl.eval one fuel state with
        | mk result next =>
          rw [actual] at same
          cases result with
          | error halt =>
            rw [Solidity.Yul.LocalBoolItems.run]
            dsimp only [Solidity.Yul.LocalExprStatement.discard]
            rw [actual]
            exact same
          | ok value =>
            rw [Solidity.Yul.LocalBoolItems.run]
            dsimp only [Solidity.Yul.LocalExprStatement.discard]
            rw [actual]
            exact (ih (fuel+1) next).trans same
  | @declaration types out init rest one tail ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
        have same := Solidity.Yul.LocalBoolControl.world one fuel state
        cases actual : Solidity.Yul.LocalBoolControl.eval one fuel state with
        | mk result next =>
          rw [actual] at same
          cases result with
          | error halt =>
            rw [Solidity.Yul.LocalBoolItems.run]
            dsimp only [Solidity.Yul.LocalBoolInitialization.run,Solidity.Yul.LocalBoolInitialization.finish]
            rw [actual]
            exact same
          | ok value =>
            rw [Solidity.Yul.LocalBoolItems.run]
            dsimp only [Solidity.Yul.LocalBoolInitialization.run,Solidity.Yul.LocalBoolInitialization.finish]
            rw [actual]
            exact (ih (fuel+1) ((value,next.1),next.2)).trans same

theorem default_run : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalItemWorld.world (Solidity.Yul.LocalDefaultItems.run proof fuel state) = state.2 := by

  intro env returns modifier control types out items proof fuel state
  induction proof generalizing fuel with
  | body body =>
    exact Solidity.Yul.LocalItemWorld.bool_run env returns modifier control _ _ _ body fuel state
  | @declaration types out ty rest value tail ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
        cases fuel with
        | zero => rfl
        | succ fuel =>
          rw [Solidity.Yul.LocalDefaultItems.run]
          dsimp only []
          exact ih (fuel+2) ((.clean value.value,state.1),state.2)

theorem close_world : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control items) (result : Solidity.Yul.LocalBoolItems.Result env out),
 Solidity.Yul.LocalItemWorld.world (Solidity.Yul.LocalDefaultItems.close proof result) =
 Solidity.Yul.LocalItemWorld.world result := by

  intro env returns modifier control types out items proof result
  cases result <;> rfl

theorem default_block : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalItemWorld.world (Solidity.Yul.LocalDefaultItems.blockRun proof fuel state) = state.2 := by

  intro env returns modifier control types out items proof fuel state
  cases fuel with
  | zero => rfl
  | succ fuel =>
    change Solidity.Yul.LocalItemWorld.world
      (Solidity.Yul.LocalDefaultItems.close proof (Solidity.Yul.LocalDefaultItems.run proof fuel state)) = state.2
    rw [Solidity.Yul.LocalItemWorld.close_world,Solidity.Yul.LocalItemWorld.default_run]

theorem unchecked_run :  ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l : Bool) (types middle out : Solidity.Source.RCtx)
 (inner : Solidity.Source.RItems env returns modifier ⟨l,true⟩ types middle)
 (inside : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,true⟩ inner)
 (rest : Solidity.Source.RItems env returns modifier ⟨l,false⟩ types out)
 (tail : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,false⟩ rest)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalItemWorld.world
  (Solidity.Yul.LocalDefaultUnchecked.run inside tail fuel state) = state.2 := by

  intro env returns modifier l types middle out inner inside rest tail fuel state
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have same := Solidity.Yul.LocalItemWorld.default_run env returns modifier ⟨l,true⟩
      types middle inner inside fuel state
    cases actual : Solidity.Yul.LocalDefaultItems.run inside fuel state with
    | halted halt next =>
      rw [actual] at same
      rw [Solidity.Yul.LocalDefaultUnchecked.run,actual]
      exact same
    | normal next =>
      rw [actual] at same
      rw [Solidity.Yul.LocalDefaultUnchecked.run,actual]
      dsimp only [Solidity.Yul.LocalDefaultItems.close]
      exact (Solidity.Yul.LocalItemWorld.default_run env returns modifier ⟨l,false⟩
        types out rest tail fuel (Solidity.Yul.LocalDefaultItems.restore inside next)).trans same

theorem unchecked_block :  ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l : Bool) (types middle out : Solidity.Source.RCtx)
 (inner : Solidity.Source.RItems env returns modifier ⟨l,true⟩ types middle)
 (inside : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,true⟩ inner)
 (rest : Solidity.Source.RItems env returns modifier ⟨l,false⟩ types out)
 (tail : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,false⟩ rest)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalItemWorld.world
  (Solidity.Yul.LocalDefaultUnchecked.blockRun inside tail fuel state) = state.2 := by

  intro env returns modifier l types middle out inner inside rest tail fuel state
  cases fuel with
  | zero => rfl
  | succ fuel =>
    change Solidity.Yul.LocalItemWorld.world
      (Solidity.Yul.LocalDefaultItems.close tail
        (Solidity.Yul.LocalDefaultUnchecked.run inside tail fuel state)) = state.2
    rw [Solidity.Yul.LocalItemWorld.close_world,Solidity.Yul.LocalItemWorld.unchecked_run]

/-- Observations that depend only on the world are preserved, on arbitrary raw inputs. -/
theorem observe_unchecked_block :  ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l : Bool) (types middle out : Solidity.Source.RCtx)
 (inner : Solidity.Source.RItems env returns modifier ⟨l,true⟩ types middle)
 (inside : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,true⟩ inner)
 (rest : Solidity.Source.RItems env returns modifier ⟨l,false⟩ types out)
 (tail : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,false⟩ rest)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types)
 (X : Type) (view : Solidity.Source.St env → X),
 view (Solidity.Yul.LocalItemWorld.world
  (Solidity.Yul.LocalDefaultUnchecked.blockRun inside tail fuel state)) = view state.2 := by

  intro env returns modifier l types middle out inner inside rest tail fuel state X view
  exact congrArg view (Solidity.Yul.LocalItemWorld.unchecked_block env returns modifier l
    types middle out inner inside rest tail fuel state)
end Solidity.Yul.LocalItemWorld
