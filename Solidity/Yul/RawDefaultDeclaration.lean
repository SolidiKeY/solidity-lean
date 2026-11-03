import Solidity.Yul.RawLocalScope

/-! Constant-default Source declarations beside raw locals. The certificate
states the actual Source default lookup; absence says nothing about allocating
reference declarations. This is not a frontend admission certificate. -/
namespace Solidity.Yul.RawDefaultDeclaration
open RawLocalDeclaration

structure Default (env : Solidity.Source.Env) (ty : Solidity.Source.STy) where
  value : Solidity.Source.Val env.layout ty
  isDefault : Solidity.Source.Val.default env.layout ty = some value

def check (env : Solidity.Source.Env) (ty : Solidity.Source.STy) : Option (Default env ty) :=
  match found : Solidity.Source.Val.default env.layout ty with
  | none => none
  | some value => some ⟨value,found⟩

inductive Result (env : Solidity.Source.Env) (types : Solidity.Source.RCtx)
    (ty : Solidity.Source.STy) where
  | normal : Snapshot env (ty :: types) → Result env types ty
  | halted : Solidity.Source.Halt → Snapshot env types → Result env types ty

def run {env types ty} (defaultValue : Default env ty)
    (fuel : Nat) (state : Snapshot env types) : Result env types ty :=
  match fuel with
  | 0 => .halted .timeout state
  | n+1 => match n with
    | 0 => .halted .timeout state
    | _+1 => .normal ⟨.cons defaultValue.value state.clean,
        (.clean defaultValue.value,state.values),state.world⟩

def project {env types ty} (result : Result env types ty) :
    Solidity.Source.R (Solidity.Source.Out env.layout types (ty :: types)) ×
    (Solidity.Source.Locals env.layout [] × Solidity.Source.St env) :=
  Result.casesOn (motive := fun _ =>
    Solidity.Source.R (Solidity.Source.Out env.layout types (ty :: types)) ×
      (Solidity.Source.Locals env.layout [] × Solidity.Source.St env)) result
    (fun next => (.ok (.normal next.clean),(Solidity.Source.L0 env,next.world)))
    (fun halt next => (.error halt,(Solidity.Source.L0 env,next.world)))

def Preserves {env types ty} (defaultValue : Default env ty)
    (before : Snapshot env types) (result : Result env types ty) : Prop :=
  Result.casesOn (motive := fun _ => Prop) result
    (fun next =>
      next.clean = .cons defaultValue.value before.clean ∧
      next.values = (.clean defaultValue.value,before.values) ∧
      next.world = before.world)
    (fun _ next => next = before)

theorem correct : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) (ty : Solidity.Source.STy)
 (defaultValue : Solidity.Yul.RawDefaultDeclaration.Default env ty)
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph env)) (state : Solidity.Yul.RawLocalDeclaration.Snapshot env types),
 Solidity.Yul.RawDefaultDeclaration.Preserves defaultValue state
   (Solidity.Yul.RawDefaultDeclaration.run defaultValue fuel state) ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.declVar (E := env) (R := returns) (M := modifier)
     (k := control) (Γ := types) ty) state.clean).run
  (Solidity.Source.L0 env,state.world) =
  Solidity.Yul.RawDefaultDeclaration.project
    (Solidity.Yul.RawDefaultDeclaration.run defaultValue fuel state) := by
  intro env types ty defaultValue returns modifier control glob frame fuel nps ph state
  cases fuel with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel =>
    cases fuel with
    | zero => exact ⟨rfl,rfl⟩
    | succ fuel =>
      constructor
      · exact ⟨rfl,rfl,rfl⟩
      · change (do
          let (value,locals) ← Solidity.Source.EM.sub state.clean
            (Solidity.Source.zeroVal (E := env) (fuel+1) ty)
          pure (Solidity.Source.Out.normal (Solidity.Source.Locals.cons value locals))).run
          (Solidity.Source.L0 env,state.world) = _
        rw [Solidity.Source.zeroVal,defaultValue.isDefault]
        rfl

theorem int_default : ∀ (env : Solidity.Source.Env) (ty : Solidity.Source.IntTy),
 Solidity.Source.Val.default env.layout (.int ty) =
 some (Solidity.Source.Val.int 0 ty.zero_mem) := by
  intro env ty; rfl

def intDefault (env : Solidity.Source.Env) (ty : Solidity.Source.IntTy) : Default env (.int ty) :=
  ⟨.int 0 ty.zero_mem,int_default env ty⟩

theorem int_correct : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) (ty : Solidity.Source.IntTy)
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph env)) (state : Solidity.Yul.RawLocalDeclaration.Snapshot env types),
 Solidity.Yul.RawDefaultDeclaration.Preserves (Solidity.Yul.RawDefaultDeclaration.intDefault env ty)
 state (Solidity.Yul.RawDefaultDeclaration.run (Solidity.Yul.RawDefaultDeclaration.intDefault env ty) fuel state) ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.declVar (E := env) (R := returns) (M := modifier)
     (k := control) (Γ := types) (.int ty)) state.clean).run
  (Solidity.Source.L0 env,state.world) =
  Solidity.Yul.RawDefaultDeclaration.project
   (Solidity.Yul.RawDefaultDeclaration.run (Solidity.Yul.RawDefaultDeclaration.intDefault env ty) fuel state) := by
  intro env types ty returns modifier control glob frame fuel nps ph state
  exact Solidity.Yul.RawDefaultDeclaration.correct env types (.int ty)
    (Solidity.Yul.RawDefaultDeclaration.intDefault env ty) returns modifier control
    glob frame fuel nps ph state

end Solidity.Yul.RawDefaultDeclaration
