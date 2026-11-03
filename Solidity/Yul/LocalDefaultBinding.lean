import Solidity.Yul.LocalBoolItemScope
import Solidity.Yul.RawDefaultDeclaration

/-! Actual constant-default declarations followed by certified local items.
The default certificate is the real Source lookup, not an allocation promise. -/
namespace Solidity.Yul.LocalDefaultBinding

def run {env returns modifier control types out ty items}
    (value : RawDefaultDeclaration.Default env ty)
    (body : LocalBoolItems.Supported env returns modifier control
      (types := ty :: types) (out := out) items)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env out :=
  match fuel with
  | 0 => .halted .timeout state
  | fuel+1 => match fuel with
    | 0 => .halted .timeout state
    | fuel+1 => match fuel with
      | 0 => .halted .timeout state
      | fuel+1 => LocalBoolItems.run body (fuel+2) ((.clean value.value,state.1),state.2)

/-- Concrete Source declaration/body composition; requires actual constant default lookup and clean input. -/
theorem source_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (ty : Solidity.Source.STy) (value : Solidity.Yul.RawDefaultDeclaration.Default env ty)
 (items : Solidity.Source.RItems env returns modifier control (ty :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalDefaultBinding.run value body fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execItems glob frame fuel nps ph
   (.stmt (.declVar ty) items) locals).run (Solidity.Source.L0 env,world)) := by

  intro env returns modifier control types out ty value items body glob frame fuel nps ph locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
        let before : Solidity.Yul.RawLocalDeclaration.Snapshot env types :=
          ⟨locals,Solidity.Yul.LocalValues.ofClean locals,world⟩
        have declaration := (Solidity.Yul.RawDefaultDeclaration.correct env types ty value
          returns modifier control glob frame (fuel+2) nps ph before).2
        change (Solidity.Source.execS glob frame (fuel+2) nps ph (.declVar ty) locals).run
          (Solidity.Source.L0 env,world) =
          (.ok (.normal (.cons value.value locals)),(Solidity.Source.L0 env,world)) at declaration
        have tailAgreement := Solidity.Yul.LocalBoolItems.source_agrees env returns modifier control
          (ty :: types) out items body glob frame (fuel+2) nps ph (.cons value.value locals) world
        rw [Solidity.Yul.LocalDefaultBinding.run]
        change Solidity.Yul.LocalBoolItems.project types
          (Solidity.Yul.LocalBoolItems.run body (fuel+2)
            (Solidity.Yul.LocalState.ofClean (.cons value.value locals,world))) = _
        rw [Solidity.Yul.LocalBoolItems.project_up env types (ty :: types) out,tailAgreement]
        rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,declaration]
        dsimp only []
        rw [Solidity.Yul.LocalBoolItems.lift_up_run]
        rfl



/-- The default declaration and its body extend the input context by a prefix. -/
theorem suffix : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (ty : Solidity.Source.STy)
 (items : Solidity.Source.RItems env returns modifier control (ty :: types) out)
 (_body : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items),
 out.drop (out.length - types.length) = types := by

  intro env returns modifier control types out ty items body
  have enough := Solidity.Yul.LocalBoolItemScope.length_mono env returns modifier control
    (ty :: types) out items body
  have tail := Solidity.Yul.LocalBoolItemScope.suffix env returns modifier control
    (ty :: types) out items body
  have count : out.length - types.length =
      (out.length - (ty :: types).length) + 1 := by
    simp only [List.length_cons] at enough ⊢
    omega
  rw [count, ← List.drop_drop, tail] <;> rfl

def restore {env returns modifier control types out ty items}
    (body : LocalBoolItems.Supported env returns modifier control
      (types := ty :: types) (out := out) items)
    (state : LocalState env out) : LocalState env types :=
  ⟨suffix env returns modifier control types out ty items body ▸
    LocalBoolItemScope.drop (out.length - types.length) state.1,state.2⟩


theorem source_restore : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (ty : Solidity.Source.STy)
 (items : Solidity.Source.RItems env returns modifier control (ty :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items),
 ∀ (locals : Solidity.Source.Locals env.layout out),
 locals.restore types =
 .ok (Solidity.Yul.LocalDefaultBinding.suffix env returns modifier control types out ty items body ▸
    locals.drop (out.length - types.length)) := by

  intro env returns modifier control types out ty items body locals
  unfold Solidity.Source.Locals.restore
  rw [dif_pos (Solidity.Yul.LocalDefaultBinding.suffix env returns modifier control types out ty items body)] <;> rfl

theorem restore_project : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (ty : Solidity.Source.STy)
 (items : Solidity.Source.RItems env returns modifier control (ty :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items),
 ∀ (state : Solidity.Yul.LocalState env out) (locals : Solidity.Source.Locals env.layout out),
 Solidity.Yul.LocalValues.clean? out state.1 = some locals →
 Solidity.Yul.LocalValues.clean? types (Solidity.Yul.LocalDefaultBinding.restore body state).1 =
 some (Solidity.Yul.LocalDefaultBinding.suffix env returns modifier control types out ty items body ▸
    locals.drop (out.length - types.length)) := by

  intro env returns modifier control types out ty items body state locals decoded
  rcases state with ⟨values,world⟩
  have encoded := Solidity.Yul.LocalBoolItemScope.values_inverse env out values locals decoded
  rw [← encoded]
  simp only [Solidity.Yul.LocalDefaultBinding.restore,Solidity.Yul.LocalBoolItemScope.drop_clean,
    Solidity.Yul.LocalBoolItemScope.cast_clean,Solidity.Yul.LocalValues.clean_ofClean]

def close {env returns modifier control types out ty items}
    (body : LocalBoolItems.Supported env returns modifier control
      (types := ty :: types) (out := out) items)
    (result : LocalBoolItems.Result env out) : LocalBoolItems.Result env types :=
  LocalBoolItems.Result.casesOn (motive := fun _ => LocalBoolItems.Result env types) result
    (fun next => .normal (restore body next))
    (fun {_reached} halt next => .halted halt next)

def blockRun {env returns modifier control types out ty items}
    (value : RawDefaultDeclaration.Default env ty)
    (body : LocalBoolItems.Supported env returns modifier control
      (types := ty :: types) (out := out) items)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env types :=
  match fuel with
  | 0 => .halted .timeout state
  | fuel+1 => close body (run value body fuel state)


/-- Actual Source block agreement for clean input, without a supplied body-agreement premise. -/
theorem block_source_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (ty : Solidity.Source.STy)
 (items : Solidity.Source.RItems env returns modifier control (ty :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items)
 (value : Solidity.Yul.RawDefaultDeclaration.Default env ty)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalDefaultBinding.blockRun value body fuel
     (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph
   (.block (.stmt (.declVar ty) items)) locals).run (Solidity.Source.L0 env,world)) := by

  intro env returns modifier control types out ty items body value glob frame fuel nps ph locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have child := Solidity.Yul.LocalDefaultBinding.source_agrees env returns modifier control
      types out ty value items body glob frame fuel nps ph locals world
    cases actual : Solidity.Yul.LocalDefaultBinding.run value body fuel
      (Solidity.Yul.LocalState.ofClean (locals,world)) with
    | halted halt next =>
      rw [actual] at child
      change some ((Except.error halt : Solidity.Source.R (Solidity.Source.Out env.layout types out)),
        (Solidity.Source.L0 env,next.2)) = some _ at child
      have sourceChild := (Option.some.inj child).symm
      simp only [Solidity.Yul.LocalDefaultBinding.blockRun,actual,Solidity.Yul.LocalDefaultBinding.close,
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
        have restored := Solidity.Yul.LocalDefaultBinding.restore_project env returns modifier control
          types out ty items body next cleanLocals decoded
        have sourceRestore := Solidity.Yul.LocalDefaultBinding.source_restore env returns modifier control
          types out ty items body cleanLocals
        simp only [Solidity.Yul.LocalDefaultBinding.blockRun,actual,Solidity.Yul.LocalDefaultBinding.close,
          Solidity.Yul.LocalBoolItems.project,restored,Option.map_some]
        rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sourceChild]
        dsimp only []
        rw [Solidity.Source.Out.close,sourceRestore] <;> rfl



end Solidity.Yul.LocalDefaultBinding
