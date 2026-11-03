import Solidity.Yul.RawLocalDeclaration

/-! Execute the existing Boolean declaration producer and close its temporary
scope. The complete enclosing raw snapshot is restored; clean Source projection
remains separate from ordinary dirty-local reads. -/
namespace Solidity.Yul.RawLocalScope
open RawLocalDeclaration

theorem restore_cons : ∀ (layout : Solidity.Source.Layout) (types : Solidity.Source.RCtx) (ty : Solidity.Source.STy)
 (value : Solidity.Source.Val layout ty) (locals : Solidity.Source.Locals layout types),
 (Solidity.Source.Locals.cons value locals).restore types = .ok locals := by
  intro layout types ty value locals
  unfold Solidity.Source.Locals.restore
  have count : (ty :: types).length - types.length = 1 := by
    simp only [List.length_cons]
    omega
  have suffix : (ty :: types).drop ((ty :: types).length - types.length) = types := by
    rw [count]
    rfl
  rw [dif_pos suffix]
  have dropped : ∀ (k : Nat) (one : k = 1) (back : (ty :: types).drop k = types),
      (back ▸ Solidity.Source.Locals.drop k (Solidity.Source.Locals.cons value locals)) = locals := by
    intro k one back
    subst k
    rfl
  rw [dropped _ count suffix]
  rfl

def dropBool {env types} (state : Snapshot env (.bool :: types)) : Snapshot env types :=
  ⟨state.clean.drop 1,state.values.2,state.world⟩

def run {env types} (fuel : Nat) (state : Snapshot env types) :
    Solidity.Source.R (Solidity.Source.Out env.layout types types) × Snapshot env types :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 => match n with
    | 0 => (.error .timeout,state)
    | k+1 =>
      BoolResult.casesOn (motive := fun _ =>
        Solidity.Source.R (Solidity.Source.Out env.layout types types) × Snapshot env types)
        (RawLocalDeclaration.run k state)
        (fun next => let closed := dropBool next
                     (.ok (.normal closed.clean),closed))
        (fun halt previous => (.error halt,previous))

def project {env types}
    (result : Solidity.Source.R (Solidity.Source.Out env.layout types types) × Snapshot env types) :=
  (result.1,(Solidity.Source.L0 env,result.2.world))

theorem correct : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx)
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph env)) (state : Solidity.Yul.RawLocalDeclaration.Snapshot env types),
 (Solidity.Yul.RawLocalScope.run fuel state).2 = state ∧
 (Solidity.Source.execS glob frame fuel nps ph
  (Solidity.Source.RStmt.block (Solidity.Source.RItems.stmt
    (Solidity.Source.RStmt.declVar (E := env) (R := returns) (M := modifier)
      (k := control) (Γ := types) .bool) .nil)) state.clean).run
  (Solidity.Source.L0 env,state.world) =
  Solidity.Yul.RawLocalScope.project (Solidity.Yul.RawLocalScope.run fuel state) := by
  intro env types returns modifier control glob frame fuel nps ph state
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
              ((Solidity.Source.Out.normal (Solidity.Source.Locals.cons (.bool false) state.clean) :
                Solidity.Source.Out env.layout types (.bool :: types)).close)).run
              (Solidity.Source.L0 env,state.world) =
              (.ok (.normal state.clean),(Solidity.Source.L0 env,state.world))
            rw [Solidity.Source.Out.close,Solidity.Yul.RawLocalScope.restore_cons]
            rfl

def frameRun {ctx : Solidity.Source.Ctx} (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  let actual := run fuel (Snapshot.ofFrame state)
  (actual.1.map (fun _ => .normal),state)

theorem frame_correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawLocalDeclaration.Snapshot.ofFrame (Solidity.Yul.RawLocalScope.frameRun fuel state).2 =
   (Solidity.Yul.RawLocalScope.run fuel (Solidity.Yul.RawLocalDeclaration.Snapshot.ofFrame state)).2 ∧
 (Solidity.Source.execS glob frame fuel nps ph
  (Solidity.Source.RStmt.block (Solidity.Source.RItems.stmt
    (Solidity.Source.RStmt.declVar (E := ctx.env) (R := returns) (M := modifier)
      (k := ⟨true,u⟩) (Γ := ctx.tys) .bool) .nil)) state.clean).run
  (Solidity.Source.L0 ctx.env,state.world) =
  Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawLocalScope.frameRun fuel state) := by
  intro ctx returns modifier u glob frame fuel nps ph state
  have actual := Solidity.Yul.RawLocalScope.correct ctx.env ctx.tys returns modifier
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

/-- Concrete implementation of the existing same-context Source adapter. -/
def adapter {ctx returns modifier u} :
    RawSourceAdapter.Adapter ctx returns modifier u
      (.block (.stmt (.declVar .bool) .nil)) where
  run := frameRun
  correct glob frame fuel nps ph state same :=
    ⟨same,(frame_correct ctx returns modifier u glob frame fuel nps ph state).2⟩

end Solidity.Yul.RawLocalScope
