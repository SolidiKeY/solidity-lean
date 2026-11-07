import Solidity.Yul.LocalDefaultBinding

/-! Certified sequences of constant-default declarations over the existing Source syntax.
Each declaration adds its real typed value beside the surviving raw locals. -/
namespace Solidity.Yul.LocalDefaultItems

inductive Supported (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
    (modifier : Bool) (control : Solidity.Source.SCtx) :
    {types out : Solidity.Source.RCtx} →
    Solidity.Source.RItems env returns modifier control types out → Type where
  | body {types out items} :
      LocalBoolItems.Supported env returns modifier control (types := types) (out := out) items →
      Supported env returns modifier control items
  | declaration {types out ty rest} :
      RawDefaultDeclaration.Default env ty →
      Supported env returns modifier control (types := ty :: types) (out := out) rest →
      Supported env returns modifier control (.stmt (.declVar ty) rest)

def run {env returns modifier control types out items}
    (proof : Supported env returns modifier control (types := types) (out := out) items) :
    Nat → LocalState env types → LocalBoolItems.Result env out := by
  apply Supported.casesOn (motive := fun {types out} _ _ =>
    Nat → LocalState env types → LocalBoolItems.Result env out) proof
  case body =>
    intro types out items body
    exact LocalBoolItems.run body
  case declaration =>
    intro types out ty rest value tail
    exact fun fuel state => match fuel with
      | 0 => .halted .timeout state
      | fuel+1 => match fuel with
        | 0 => .halted .timeout state
        | fuel+1 => match fuel with
          | 0 => .halted .timeout state
          | fuel+1 => run tail (fuel+2) ((.clean value.value,state.1),state.2)
termination_by structural proof


/-- Concrete Source item agreement from clean input for every certified declaration sequence. -/
theorem source_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalDefaultItems.run proof fuel
     (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execItems glob frame fuel nps ph items locals).run
   (Solidity.Source.L0 env,world)) := by

  intro env returns modifier control types out items proof glob frame fuel nps ph locals world
  induction proof generalizing fuel world with
  | body body =>
    exact Solidity.Yul.LocalBoolItems.source_agrees env returns modifier control
      _ _ _ body glob frame fuel nps ph locals world
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
          let before : Solidity.Yul.RawLocalDeclaration.Snapshot env types :=
            ⟨locals,Solidity.Yul.LocalValues.ofClean locals,world⟩
          have declaration := (Solidity.Yul.RawDefaultDeclaration.correct env types ty value
            returns modifier control glob frame (fuel+2) nps ph before).2
          change (Solidity.Source.execS glob frame (fuel+2) nps ph (.declVar ty) locals).run
            (Solidity.Source.L0 env,world) =
            (.ok (.normal (.cons value.value locals)),(Solidity.Source.L0 env,world)) at declaration
          have tailAgreement := ih (fuel+2) (.cons value.value locals) world
          rw [Solidity.Yul.LocalDefaultItems.run]
          change Solidity.Yul.LocalBoolItems.project types
            (Solidity.Yul.LocalDefaultItems.run tail (fuel+2)
              (Solidity.Yul.LocalState.ofClean (.cons value.value locals,world))) = _
          rw [Solidity.Yul.LocalBoolItems.project_up env types (ty :: types) out,tailAgreement]
          rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,declaration]
          dsimp only []
          rw [Solidity.Yul.LocalBoolItems.lift_up_run]
          rfl


/-- Every certified sequence adds only a typed local prefix. -/
theorem context : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (_proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control items),
 types.length ≤ out.length ∧ out.drop (out.length - types.length) = types := by

  intro env returns modifier control types out items proof
  induction proof with
  | body body =>
    exact ⟨Solidity.Yul.LocalBoolItemScope.length_mono env returns modifier control _ _ _ body,
      Solidity.Yul.LocalBoolItemScope.suffix env returns modifier control _ _ _ body⟩
  | @declaration types out ty rest value tail ih =>
    have enough : (ty :: types).length ≤ out.length := ih.1
    have count : out.length - types.length =
        (out.length - (ty :: types).length) + 1 := by
      simp only [List.length_cons] at enough ⊢
      omega
    constructor
    · simp only [List.length_cons] at enough
      omega
    · rw [count, ← List.drop_drop, ih.2] <;> rfl

def restore {env returns modifier control types out items}
    (proof : Supported env returns modifier control (types := types) (out := out) items)
    (state : LocalState env out) : LocalState env types :=
  ⟨(context env returns modifier control types out items proof).2 ▸
    LocalBoolItemScope.drop (out.length - types.length) state.1,state.2⟩

def close {env returns modifier control types out items}
    (proof : Supported env returns modifier control (types := types) (out := out) items)
    (result : LocalBoolItems.Result env out) : LocalBoolItems.Result env types :=
  LocalBoolItems.Result.casesOn (motive := fun _ => LocalBoolItems.Result env types) result
    (fun next => .normal (restore proof next))
    (fun {_reached} halt next => .halted halt next)

def blockRun {env returns modifier control types out items}
    (proof : Supported env returns modifier control (types := types) (out := out) items)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env types :=
  match fuel with
  | 0 => .halted .timeout state
  | fuel+1 => close proof (run proof fuel state)


theorem source_restore : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control items),
 ∀ (locals : Solidity.Source.Locals env.layout out),
 locals.restore types =
 .ok ((Solidity.Yul.LocalDefaultItems.context env returns modifier control types out items proof).2 ▸
    locals.drop (out.length - types.length)) := by

  intro env returns modifier control types out items proof locals
  unfold Solidity.Source.Locals.restore
  rw [dif_pos (Solidity.Yul.LocalDefaultItems.context env returns modifier control types out items proof).2] <;> rfl

theorem restore_project : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control items),
 ∀ (state : Solidity.Yul.LocalState env out) (locals : Solidity.Source.Locals env.layout out),
 Solidity.Yul.LocalValues.clean? out state.1 = some locals →
 Solidity.Yul.LocalValues.clean? types (Solidity.Yul.LocalDefaultItems.restore proof state).1 =
 some ((Solidity.Yul.LocalDefaultItems.context env returns modifier control types out items proof).2 ▸
    locals.drop (out.length - types.length)) := by

  intro env returns modifier control types out items proof state locals decoded
  rcases state with ⟨values,world⟩
  have encoded := Solidity.Yul.LocalBoolItemScope.values_inverse env out values locals decoded
  rw [← encoded]
  simp only [Solidity.Yul.LocalDefaultItems.restore,Solidity.Yul.LocalBoolItemScope.drop_clean,
    Solidity.Yul.LocalBoolItemScope.cast_clean,Solidity.Yul.LocalValues.clean_ofClean]


/-- Actual Source block agreement, from clean input and concrete certified execution. -/
theorem block_source_agrees :  ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalDefaultItems.blockRun proof fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph (.block items) locals).run
   (Solidity.Source.L0 env,world)) := by

  intro env returns modifier control types out items proof glob frame fuel nps ph locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have child := Solidity.Yul.LocalDefaultItems.source_agrees env returns modifier control
      types out items proof glob frame fuel nps ph locals world
    cases actual : Solidity.Yul.LocalDefaultItems.run proof fuel
      (Solidity.Yul.LocalState.ofClean (locals,world)) with
    | halted halt next =>
      rw [actual] at child
      change some ((Except.error halt : Solidity.Source.R (Solidity.Source.Out env.layout types out)),
        (Solidity.Source.L0 env,next.2)) = some _ at child
      have sourceChild := (Option.some.inj child).symm
      simp only [Solidity.Yul.LocalDefaultItems.blockRun,actual,Solidity.Yul.LocalDefaultItems.close,
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
        have restored := Solidity.Yul.LocalDefaultItems.restore_project env returns modifier control
          types out items proof next cleanLocals decoded
        have sourceRestore := Solidity.Yul.LocalDefaultItems.source_restore env returns modifier control
          types out items proof cleanLocals
        simp only [Solidity.Yul.LocalDefaultItems.blockRun,actual,Solidity.Yul.LocalDefaultItems.close,
          Solidity.Yul.LocalBoolItems.project,restored,Option.map_some]
        rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sourceChild]
        dsimp only []
        rw [Solidity.Source.Out.close,sourceRestore] <;> rfl



end Solidity.Yul.LocalDefaultItems
