import Solidity.Yul.LocalBoolItems
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


end Solidity.Yul.LocalDefaultBinding
