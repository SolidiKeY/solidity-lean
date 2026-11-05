import Solidity.Yul.RawIntegerInitialization
import Solidity.Yul.RawPreparedDeclaration

/-! In-range integer literal declarations in the existing named raw frame.
The real snapshot initializer is reused. Older authoritative words are prepared
without truncation; Source projection observes stored clean locals explicitly.
This is not arbitrary integer expression or dirty ordinary readback admission. -/
namespace Solidity.Yul.RawPreparedInteger
def run {ctx : Solidity.Source.Ctx} (name : String) (ty : Solidity.Source.IntTy)
    (value : Int) (inRange : ty.lo ≤ value ∧ value ≤ ty.hi)
    (fuel : Nat) (state : RawFrame.State ctx) :
    Sum (Solidity.Source.Halt × RawFrame.State ctx)
      (RawFrame.State (ctx.push name (.int ty))) :=
  RawDefaultDeclaration.Result.casesOn (motive := fun _ =>
    Sum (Solidity.Source.Halt × RawFrame.State ctx)
      (RawFrame.State (ctx.push name (.int ty))))
    (RawIntegerInitialization.run ty value inRange fuel (RawPreparedDeclaration.input state))
    (fun next => .inr (RawDeclarationFrame.ofSnapshot (ctx := ctx.push name (.int ty)) next))
    (fun halt _previous => .inl (halt,state))
def project {ctx : Solidity.Source.Ctx} {name : String} {ty : Solidity.Source.IntTy}
    (result : Sum (Solidity.Source.Halt × RawFrame.State ctx)
      (RawFrame.State (ctx.push name (.int ty)))) :
    Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys (.int ty :: ctx.tys)) ×
      (Solidity.Source.Locals ctx.env.layout [] × Solidity.Source.St ctx.env) :=
  match result with
  | .inl failure => (.error failure.1,(Solidity.Source.L0 ctx.env,failure.2.world))
  | .inr next => (.ok (.normal next.clean),(Solidity.Source.L0 ctx.env,next.world))
end Solidity.Yul.RawPreparedInteger

namespace Solidity.Yul.RawPreparedInteger
theorem run_zero : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.IntTy)
 (value : Int) (inRange : ty.lo ≤ value ∧ value ≤ ty.hi) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawPreparedInteger.run name ty value inRange 0 state = .inl (.timeout,state) := by
  intro ctx name ty value inRange state
  rfl

theorem run_one : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.IntTy)
 (value : Int) (inRange : ty.lo ≤ value ∧ value ≤ ty.hi) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawPreparedInteger.run name ty value inRange 1 state = .inl (.timeout,state) := by
  intro ctx name ty value inRange state
  rfl

theorem run_success : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.IntTy)
 (value : Int) (inRange : ty.lo ≤ value ∧ value ≤ ty.hi) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawPreparedInteger.run name ty value inRange (fuel+2) state = .inr
 (Solidity.Yul.RawDeclarationFrame.ofSnapshot (ctx := ctx.push name (.int ty))
  ⟨.cons (.int value inRange) state.clean,
   (.clean (.int value inRange),(Solidity.Yul.RawCoherent.prepare state).1),state.world⟩) := by
  intro ctx name ty value inRange fuel state
  rfl

theorem coherent_result : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.IntTy)
 (value : Int) (inRange : ty.lo ≤ value ∧ value ≤ ty.hi) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawCoherent.coherent state = true →
 match Solidity.Yul.RawPreparedInteger.run name ty value inRange fuel state with
 | .inl failure => Solidity.Yul.RawCoherent.coherent failure.2 = true
 | .inr next => Solidity.Yul.RawCoherent.coherent next = true := by
  intro ctx name ty value inRange fuel state same
  cases fuel with
  | zero => exact same
  | succ fuel =>
    cases fuel with
    | zero => exact same
    | succ fuel =>
      rw [run_success,RawCoherent.prepare_coherent state same]
      exact (RawCoherent.coherent_iff _).mpr rfl

theorem source_correct : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.IntTy)
 (value : Int) (inRange : ty.lo ≤ value ∧ value ≤ ty.hi) (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Source.execS glob frame fuel nps ph
  (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
   (k := control) (Γ := ctx.tys) (τ := .int ty) (.const (Solidity.Source.Q.ofInt value))
   (Solidity.Yul.RawIntegerInitialization.admissible ctx.env ty value inRange)) state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) = Solidity.Yul.RawPreparedInteger.project (Solidity.Yul.RawPreparedInteger.run name ty value inRange fuel state) := by
  intro ctx name ty value inRange returns modifier control glob frame fuel nps ph state
  have first := RawIntegerInitialization.correct ctx.env ctx.tys ty value inRange
    returns modifier control glob frame fuel nps ph (RawPreparedDeclaration.input state)
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      simpa only [RawIntegerInitialization.run,RawDefaultDeclaration.project,run,project,
        RawPreparedDeclaration.input,RawDeclarationFrame.ofSnapshot,RawFrame.capture,RawFrame.ofClean]
        using first.2

end Solidity.Yul.RawPreparedInteger
