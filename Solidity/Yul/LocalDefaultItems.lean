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

end Solidity.Yul.LocalDefaultItems
