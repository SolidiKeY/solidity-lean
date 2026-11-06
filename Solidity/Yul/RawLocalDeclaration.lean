import Solidity.Yul.RawSourceVoidReturn

/-! An additive context-indexed local snapshot for an executed Boolean
declaration. Locals reuse the existing context-computed LocalValues product.
Stored clean values and authoritative raw values remain separate; no ordinary
dirty-read policy or restoration into a named frontend context is inferred. -/
namespace Solidity.Yul.RawLocalDeclaration

structure Snapshot (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) where
  clean : Solidity.Source.Locals env.layout types
  values : LocalValues env types
  world : Solidity.Source.St env

def Snapshot.ofFrame {ctx : Solidity.Source.Ctx} (state : RawFrame.State ctx) :
    Snapshot ctx.env ctx.tys :=
  ⟨state.clean,(RawFrame.materialize state).1,state.world⟩

/-- The failure branch retains the input context; success has one new Boolean.
This outcome is specific to a single declaration, not arbitrary sequencing. -/
inductive BoolResult (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) where
  | normal : Snapshot env (.bool :: types) → BoolResult env types
  | halted : Solidity.Source.Halt → Snapshot env types → BoolResult env types

def run {env types} (fuel : Nat) (state : Snapshot env types) : BoolResult env types :=
  match fuel with
  | 0 => .halted .timeout state
  | n+1 => match n with
    | 0 => .halted .timeout state
    | _+1 => .normal ⟨.cons (.bool false) state.clean,(.clean (.bool false),state.values),state.world⟩

def project {env types} (result : BoolResult env types) :
    Solidity.Source.R (Solidity.Source.Out env.layout types (.bool :: types)) ×
    (Solidity.Source.Locals env.layout [] × Solidity.Source.St env) :=
  BoolResult.casesOn (motive := fun _ =>
    Solidity.Source.R (Solidity.Source.Out env.layout types (.bool :: types)) ×
      (Solidity.Source.Locals env.layout [] × Solidity.Source.St env)) result
    (fun next => (.ok (.normal next.clean),(Solidity.Source.L0 env,next.world)))
    (fun halt next => (.error halt,(Solidity.Source.L0 env,next.world)))

def Preserves {env types} (before : Snapshot env types) (result : BoolResult env types) : Prop :=
  BoolResult.casesOn (motive := fun _ => Prop) result
    (fun next =>
      next.clean = .cons (.bool false) before.clean ∧
      next.values = (.clean (.bool false),before.values) ∧
      next.world = before.world)
    (fun _ next => next = before)

theorem correct : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx)
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph env)) (state : Solidity.Yul.RawLocalDeclaration.Snapshot env types),
 Solidity.Yul.RawLocalDeclaration.Preserves state (Solidity.Yul.RawLocalDeclaration.run fuel state) ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.declVar (E := env) (R := returns) (M := modifier)
     (k := control) (Γ := types) .bool) state.clean).run
  (Solidity.Source.L0 env,state.world) =
  Solidity.Yul.RawLocalDeclaration.project (Solidity.Yul.RawLocalDeclaration.run fuel state) := by
  intro env types returns modifier control glob frame fuel nps ph state
  cases fuel with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel =>
    cases fuel with
    | zero => exact ⟨rfl,rfl⟩
    | succ fuel => exact ⟨⟨rfl,rfl,rfl⟩,rfl⟩

end Solidity.Yul.RawLocalDeclaration
