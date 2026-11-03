import Solidity.Yul.RawDefaultDeclaration

/-! Execute a certified constant-default declaration and close its local scope.
This composes concrete producer bodies. It does not supply arbitrary initializers
or a dirty-read policy, and the real default certificate is retained. -/
namespace Solidity.Yul.RawDefaultScope
open RawLocalDeclaration RawDefaultDeclaration

def drop {env types ty} (state : Snapshot env (ty :: types)) : Snapshot env types :=
  ⟨state.clean.drop 1,state.values.2,state.world⟩

def run {env types ty} (defaultValue : Default env ty)
    (fuel : Nat) (state : Snapshot env types) :
    Solidity.Source.R (Solidity.Source.Out env.layout types types) × Snapshot env types :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 => match n with
    | 0 => (.error .timeout,state)
    | k+1 =>
      Result.casesOn (motive := fun _ =>
        Solidity.Source.R (Solidity.Source.Out env.layout types types) × Snapshot env types)
        (RawDefaultDeclaration.run defaultValue k state)
        (fun next => let closed := drop next
                     (.ok (.normal closed.clean),closed))
        (fun halt previous => (.error halt,previous))

def project {env types}
    (result : Solidity.Source.R (Solidity.Source.Out env.layout types types) × Snapshot env types) :=
  (result.1,(Solidity.Source.L0 env,result.2.world))

theorem correct : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) (ty : Solidity.Source.STy)
 (defaultValue : Solidity.Yul.RawDefaultDeclaration.Default env ty)
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph env)) (state : Solidity.Yul.RawLocalDeclaration.Snapshot env types),
 (Solidity.Yul.RawDefaultScope.run defaultValue fuel state).2 = state ∧
 (Solidity.Source.execS glob frame fuel nps ph
  (Solidity.Source.RStmt.block (Solidity.Source.RItems.stmt
    (Solidity.Source.RStmt.declVar (E := env) (R := returns) (M := modifier)
      (k := control) (Γ := types) ty) .nil)) state.clean).run
  (Solidity.Source.L0 env,state.world) =
  Solidity.Yul.RawDefaultScope.project (Solidity.Yul.RawDefaultScope.run defaultValue fuel state) := by
  intro env types ty defaultValue returns modifier control glob frame fuel nps ph state
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
          · simp only [Solidity.Source.execS,Solidity.Source.execItems,
              Solidity.Source.zeroVal,defaultValue.isDefault]
            change (Solidity.Source.EM.lift
              ((Solidity.Source.Out.normal (Solidity.Source.Locals.cons defaultValue.value state.clean) :
                Solidity.Source.Out env.layout types (ty :: types)).close)).run
              (Solidity.Source.L0 env,state.world) =
              (.ok (.normal state.clean),(Solidity.Source.L0 env,state.world))
            rw [Solidity.Source.Out.close,Solidity.Yul.RawLocalScope.restore_cons]
            rfl

def frameRun {ctx : Solidity.Source.Ctx} {ty} (defaultValue : Default ctx.env ty)
    (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  let actual := run defaultValue fuel (Snapshot.ofFrame state)
  (actual.1.map (fun _ => .normal),state)

theorem frame_correct : ∀ (ctx : Solidity.Source.Ctx) (ty : Solidity.Source.STy)
 (defaultValue : Solidity.Yul.RawDefaultDeclaration.Default ctx.env ty)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawLocalDeclaration.Snapshot.ofFrame (Solidity.Yul.RawDefaultScope.frameRun defaultValue fuel state).2 =
   (Solidity.Yul.RawDefaultScope.run defaultValue fuel (Solidity.Yul.RawLocalDeclaration.Snapshot.ofFrame state)).2 ∧
 (Solidity.Source.execS glob frame fuel nps ph
  (Solidity.Source.RStmt.block (Solidity.Source.RItems.stmt
    (Solidity.Source.RStmt.declVar (E := ctx.env) (R := returns) (M := modifier)
      (k := ⟨true,u⟩) (Γ := ctx.tys) ty) .nil)) state.clean).run
  (Solidity.Source.L0 ctx.env,state.world) =
  Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawDefaultScope.frameRun defaultValue fuel state) := by
  intro ctx ty defaultValue returns modifier u glob frame fuel nps ph state
  have actual := Solidity.Yul.RawDefaultScope.correct ctx.env ctx.tys ty defaultValue returns modifier
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

theorem int_correct : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) (ty : Solidity.Source.IntTy)
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph env)) (state : Solidity.Yul.RawLocalDeclaration.Snapshot env types),
 (Solidity.Yul.RawDefaultScope.run (Solidity.Yul.RawDefaultDeclaration.intDefault env ty) fuel state).2 = state ∧
 (Solidity.Source.execS glob frame fuel nps ph
  (Solidity.Source.RStmt.block (Solidity.Source.RItems.stmt
    (Solidity.Source.RStmt.declVar (E := env) (R := returns) (M := modifier)
      (k := control) (Γ := types) (.int ty)) .nil)) state.clean).run
  (Solidity.Source.L0 env,state.world) =
  Solidity.Yul.RawDefaultScope.project
   (Solidity.Yul.RawDefaultScope.run (Solidity.Yul.RawDefaultDeclaration.intDefault env ty) fuel state) := by
  intro env types ty returns modifier control glob frame fuel nps ph state
  exact Solidity.Yul.RawDefaultScope.correct env types (.int ty)
    (Solidity.Yul.RawDefaultDeclaration.intDefault env ty) returns modifier control
    glob frame fuel nps ph state

def adapter {ctx ty returns modifier u} (defaultValue : Default ctx.env ty) :
    RawSourceAdapter.Adapter ctx returns modifier u
      (.block (.stmt (.declVar ty) .nil)) where
  run := frameRun defaultValue
  correct glob frame fuel nps ph state same :=
    ⟨same,(frame_correct ctx ty defaultValue returns modifier u glob frame fuel nps ph state).2⟩

def intAdapter {ctx returns modifier u} (ty : Solidity.Source.IntTy) :
    RawSourceAdapter.Adapter ctx returns modifier u
      (.block (.stmt (.declVar (.int ty)) .nil)) :=
  adapter (intDefault ctx.env ty)

end Solidity.Yul.RawDefaultScope
