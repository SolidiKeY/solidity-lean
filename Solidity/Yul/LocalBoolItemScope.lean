import Solidity.Yul.LocalBoolItems

/-! Typed suffix restoration for scopes containing certified Boolean item lists.
Raw values are dropped by context position, never decoded or cleaned. -/
namespace Solidity.Yul.LocalBoolItemScope

def drop {env} : (count : Nat) → {types : Solidity.Source.RCtx} →
    LocalValues env types → LocalValues env (types.drop count)
  | 0, _, values => values
  | _+1, [], _ => ()
  | count+1, _ :: _, values => drop count values.2



theorem length_mono : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items),
 types.length ≤ out.length := by
  intro env returns modifier control types out items proof
  induction proof with
  | nil => exact Nat.le_refl _
  | expression _ _ ih => exact ih
  | declaration _ _ ih =>
    simp only [List.length_cons] at ih
    omega


theorem value_inverse : ∀ (env : Solidity.Source.Env) (ty : Solidity.Source.STy)
 (value : Solidity.Yul.LocalValue env ty) (decoded : Solidity.Source.Val env.layout ty),
 value.clean? = some decoded → Solidity.Yul.LocalValue.clean decoded = value := by
  intro env ty value decoded found
  cases value with
  | clean actual =>
    change some actual = some decoded at found
    cases found
    rfl
  | scalar shape raw => cases found
  | externalFunction params rets mutability address selector => cases found


theorem drop_clean : ∀ (env : Solidity.Source.Env) (count : Nat) (types : Solidity.Source.RCtx)
 (locals : Solidity.Source.Locals env.layout types),
 Solidity.Yul.LocalBoolItemScope.drop count (Solidity.Yul.LocalValues.ofClean locals) =
 Solidity.Yul.LocalValues.ofClean (locals.drop count) := by
  intro env count
  induction count with
  | zero => intro types locals; rfl
  | succ count ih =>
    intro types locals
    cases locals with
    | nil => rfl
    | cons value rest => exact ih _ rest




theorem suffix : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items),
 out.drop (out.length - types.length) = types := by
  intro env returns modifier control types out items proof
  induction proof with
  | nil => simp only [Nat.sub_self,List.drop_zero]
  | expression _ _ ih => exact ih
  | @declaration types out init rest one tail ih =>
    have enough := Solidity.Yul.LocalBoolItemScope.length_mono env returns modifier control
      (.bool :: types) out rest tail
    have count : out.length - types.length =
        (out.length - (.bool :: types).length) + 1 := by
      simp only [List.length_cons] at enough ⊢
      omega
    rw [count,← List.drop_drop,ih] <;> rfl


theorem values_inverse : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx)
 (values : Solidity.Yul.LocalValues env types) (locals : Solidity.Source.Locals env.layout types),
 Solidity.Yul.LocalValues.clean? types values = some locals →
 Solidity.Yul.LocalValues.ofClean locals = values := by
  intro env types
  induction types with
  | nil =>
    intro values locals found
    cases locals
    cases values
    rfl
  | cons ty types ih =>
    intro values locals found
    cases head : values.1.clean? with
    | none =>
      simp only [Solidity.Yul.LocalValues.clean?,head,Option.bind_none] at found
      cases found
    | some value =>
      cases tail : Solidity.Yul.LocalValues.clean? types values.2 with
      | none =>
        simp only [Solidity.Yul.LocalValues.clean?,head,tail,Option.bind_some,Option.bind_none] at found
        cases found
      | some rest =>
        simp only [Solidity.Yul.LocalValues.clean?,head,tail,Option.bind_some,Option.pure_def] at found
        cases found
        change (Solidity.Yul.LocalValue.clean value,Solidity.Yul.LocalValues.ofClean rest) = values
        exact Prod.ext (Solidity.Yul.LocalBoolItemScope.value_inverse env ty values.1 value head)
          (ih values.2 rest tail)


theorem cast_clean : ∀ (env : Solidity.Source.Env) (before after : Solidity.Source.RCtx)
 (same : before = after) (locals : Solidity.Source.Locals env.layout before),
 same ▸ Solidity.Yul.LocalValues.ofClean locals =
 Solidity.Yul.LocalValues.ofClean (same ▸ locals) := by
  intro env before after same locals
  cases same
  rfl


def restore {env returns modifier control types out items}
    (proof : LocalBoolItems.Supported env returns modifier control (types := types) (out := out) items)
    (state : LocalState env out) : LocalState env types :=
  ⟨suffix env returns modifier control types out items proof ▸
      drop (out.length - types.length) state.1,state.2⟩

def close {env returns modifier control types out items}
    (proof : LocalBoolItems.Supported env returns modifier control (types := types) (out := out) items)
    (result : LocalBoolItems.Result env out) : LocalBoolItems.Result env types :=
  LocalBoolItems.Result.casesOn (motive := fun _ => LocalBoolItems.Result env types) result
    (fun next => .normal (restore proof next))
    (fun {_reached} halt next => .halted halt next)

def run {env returns modifier control types out items}
    (proof : LocalBoolItems.Supported env returns modifier control (types := types) (out := out) items)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env types :=
  match fuel with
  | 0 => .halted .timeout state
  | fuel+1 => close proof (LocalBoolItems.run proof fuel state)



theorem source_restore : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items),
 ∀ (locals : Solidity.Source.Locals env.layout out),
 locals.restore types =
 .ok (Solidity.Yul.LocalBoolItemScope.suffix env returns modifier control types out items proof ▸
    locals.drop (out.length - types.length)) := by
  intro env returns modifier control types out items proof locals
  unfold Solidity.Source.Locals.restore
  rw [dif_pos (Solidity.Yul.LocalBoolItemScope.suffix env returns modifier control types out items proof)] <;> rfl


theorem restore_project : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items),
 ∀ (state : Solidity.Yul.LocalState env out) (locals : Solidity.Source.Locals env.layout out),
 Solidity.Yul.LocalValues.clean? out state.1 = some locals →
 Solidity.Yul.LocalValues.clean? types (Solidity.Yul.LocalBoolItemScope.restore proof state).1 =
 some (Solidity.Yul.LocalBoolItemScope.suffix env returns modifier control types out items proof ▸
    locals.drop (out.length - types.length)) := by
  intro env returns modifier control types out items proof state locals decoded
  rcases state with ⟨values,world⟩
  have encoded := Solidity.Yul.LocalBoolItemScope.values_inverse env out values locals decoded
  rw [← encoded]
  simp only [Solidity.Yul.LocalBoolItemScope.restore,Solidity.Yul.LocalBoolItemScope.drop_clean,
    Solidity.Yul.LocalBoolItemScope.cast_clean,Solidity.Yul.LocalValues.clean_ofClean]




theorem source_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalBoolItemScope.run proof fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph (.block items) locals).run
   (Solidity.Source.L0 env,world)) := by
  intro env returns modifier control types out items proof glob frame fuel nps ph locals world
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have child := Solidity.Yul.LocalBoolItems.source_agrees env returns modifier control
      types out items proof glob frame fuel nps ph locals world
    cases actual : Solidity.Yul.LocalBoolItems.run proof fuel
      (Solidity.Yul.LocalState.ofClean (locals,world)) with
    | halted halt next =>
      rw [actual] at child
      change some ((Except.error halt : Solidity.Source.R (Solidity.Source.Out env.layout types out)),
        (Solidity.Source.L0 env,next.2)) = some _ at child
      have sourceChild := (Option.some.inj child).symm
      simp only [Solidity.Yul.LocalBoolItemScope.run,actual,Solidity.Yul.LocalBoolItemScope.close,
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
        have restored := Solidity.Yul.LocalBoolItemScope.restore_project env returns modifier control
          types out items proof next cleanLocals decoded
        have sourceRestore := Solidity.Yul.LocalBoolItemScope.source_restore env returns modifier control
          types out items proof cleanLocals
        simp only [Solidity.Yul.LocalBoolItemScope.run,actual,Solidity.Yul.LocalBoolItemScope.close,
          Solidity.Yul.LocalBoolItems.project,restored,Option.map_some]
        rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,sourceChild]
        dsimp only []
        rw [Solidity.Source.Out.close,sourceRestore] <;> rfl


end Solidity.Yul.LocalBoolItemScope
