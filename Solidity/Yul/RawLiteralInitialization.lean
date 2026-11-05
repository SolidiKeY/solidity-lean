import Solidity.Yul.RawDefaultScope

/-! Executed Boolean literal initialization. Reuses existing intrinsic snapshots
and parameter-only declaration results, preserving all older raw locals.
This is not arbitrary initializer execution or an ordinary dirty-read policy. -/
namespace Solidity.Yul.RawLiteralInitialization
open RawLocalDeclaration RawDefaultDeclaration

def run {env types} (value : Bool) (fuel : Nat) (state : Snapshot env types) :
    Result env types .bool :=
  match fuel with
  | 0 => .halted .timeout state
  | n+1 => match n with
    | 0 => .halted .timeout state
    | _+1 => .normal ⟨.cons (.bool value) state.clean,
        (.clean (.bool value),state.values),state.world⟩

def Preserves {env types} (value : Bool) (before : Snapshot env types)
    (result : Result env types .bool) : Prop :=
  Result.casesOn (motive := fun _ => Prop) result
    (fun next =>
      next.clean = .cons (.bool value) before.clean ∧
      next.values = (.clean (.bool value),before.values) ∧
      next.world = before.world)
    (fun _ next => next = before)

theorem correct : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) (value : Bool)
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph env)) (state : Solidity.Yul.RawLocalDeclaration.Snapshot env types),
 Solidity.Yul.RawLiteralInitialization.Preserves value state
   (Solidity.Yul.RawLiteralInitialization.run value fuel state) ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.declInit (E := env) (R := returns) (M := modifier)
     (k := control) (Γ := types) (τ := .bool) (.bool value) (by rfl)) state.clean).run
  (Solidity.Source.L0 env,state.world) =
  Solidity.Yul.RawDefaultDeclaration.project (Solidity.Yul.RawLiteralInitialization.run value fuel state) := by
  intro env types value returns modifier control glob frame fuel nps ph state
  cases fuel with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel =>
    cases fuel with
    | zero => exact ⟨rfl,rfl⟩
    | succ fuel => exact ⟨⟨rfl,rfl,rfl⟩,rfl⟩

end Solidity.Yul.RawLiteralInitialization
