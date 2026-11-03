import Solidity.Yul.RawLiteralInitialization

/-! Execute a Boolean literal declaration and close its scope using the concrete
initializer producer. No ordinary dirty-read or arbitrary initializer policy. -/
namespace Solidity.Yul.RawLiteralScope
open RawLocalDeclaration RawDefaultDeclaration

def run {env types} (value : Bool)
    (fuel : Nat) (state : Snapshot env types) :
    Solidity.Source.R (Solidity.Source.Out env.layout types types) × Snapshot env types :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 => match n with
    | 0 => (.error .timeout,state)
    | k+1 =>
      Result.casesOn (motive := fun _ =>
        Solidity.Source.R (Solidity.Source.Out env.layout types types) × Snapshot env types)
        (RawLiteralInitialization.run value k state)
        (fun next => let closed := RawDefaultScope.drop next
                     (.ok (.normal closed.clean),closed))
        (fun halt previous => (.error halt,previous))



theorem correct :  ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) (value : Bool)
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph env)) (state : Solidity.Yul.RawLocalDeclaration.Snapshot env types),
 (Solidity.Yul.RawLiteralScope.run value fuel state).2 = state ∧
 (Solidity.Source.execS glob frame fuel nps ph
  (Solidity.Source.RStmt.block (Solidity.Source.RItems.stmt
    (Solidity.Source.RStmt.declInit (E := env) (R := returns) (M := modifier)
      (k := control) (Γ := types) (τ := .bool) (.bool value) (by rfl)) .nil)) state.clean).run
  (Solidity.Source.L0 env,state.world) =
  Solidity.Yul.RawDefaultScope.project (Solidity.Yul.RawLiteralScope.run value fuel state) := by
  intro env types value returns modifier control glob frame fuel nps ph state
  cases fuel with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel =>
    cases fuel with
    | zero => exact ⟨rfl,rfl⟩
    | succ fuel =>
      cases fuel with
      | zero => exact ⟨rfl,rfl⟩
      | succ fuel =>
        cases fuel with
        | zero => exact ⟨rfl,rfl⟩
        | succ fuel =>
          constructor
          · rfl
          · change (Solidity.Source.EM.lift
              ((Solidity.Source.Out.normal (Solidity.Source.Locals.cons (.bool value) state.clean) :
                Solidity.Source.Out env.layout types (.bool :: types)).close)).run
              (Solidity.Source.L0 env,state.world) =
              (.ok (.normal state.clean),(Solidity.Source.L0 env,state.world))
            rw [Solidity.Source.Out.close,Solidity.Yul.RawLocalScope.restore_cons]
            rfl

def frameRun {ctx : Solidity.Source.Ctx} (value : Bool)
    (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  let actual := run value fuel (Snapshot.ofFrame state)
  (actual.1.map (fun _ => .normal),state)



theorem frame_correct :  ∀ (ctx : Solidity.Source.Ctx) (value : Bool)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawLocalDeclaration.Snapshot.ofFrame (Solidity.Yul.RawLiteralScope.frameRun value fuel state).2 =
   (Solidity.Yul.RawLiteralScope.run value fuel (Solidity.Yul.RawLocalDeclaration.Snapshot.ofFrame state)).2 ∧
 (Solidity.Source.execS glob frame fuel nps ph
  (Solidity.Source.RStmt.block (Solidity.Source.RItems.stmt
    (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
      (k := ⟨true,u⟩) (Γ := ctx.tys) (τ := .bool) (.bool value) (by rfl)) .nil)) state.clean).run
  (Solidity.Source.L0 ctx.env,state.world) =
  Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawLiteralScope.frameRun value fuel state) := by
  intro ctx value returns modifier u glob frame fuel nps ph state
  have actual := Solidity.Yul.RawLiteralScope.correct ctx.env ctx.tys value returns modifier
    ⟨true,u⟩ glob frame fuel nps ph (Solidity.Yul.RawLocalDeclaration.Snapshot.ofFrame state)
  constructor
  · exact actual.1.symm
  · dsimp only [Solidity.Yul.RawLocalDeclaration.Snapshot.ofFrame] at actual
    rw [actual.2]
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
        cases fuel with
        | zero => rfl
        | succ fuel => cases fuel <;> rfl




def adapter {ctx returns modifier u} (value : Bool) :
    RawSourceAdapter.Adapter ctx returns modifier u
      (.block (.stmt (.declInit (τ := .bool) (.bool value) (by rfl)) .nil)) where
  run := frameRun value
  correct glob frame fuel nps ph state same :=
    ⟨same,(frame_correct ctx value returns modifier u glob frame fuel nps ph state).2⟩

end Solidity.Yul.RawLiteralScope
