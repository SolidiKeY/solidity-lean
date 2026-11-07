import Solidity.Yul.RawLiteralInitialization

/-! Bridge existing context-indexed declaration snapshots to the existing raw
frame of a named Source context. Capture preserves authoritative words; it
does not infer a dirty-read cleaning policy. Boolean literal declarations
extend the actual context and retain the original frame on timeout. -/
namespace Solidity.Yul.RawDeclarationFrame

def ofSnapshot {ctx : Solidity.Source.Ctx}
    (state : RawLocalDeclaration.Snapshot ctx.env ctx.tys) : RawFrame.State ctx :=
  RawFrame.capture (RawFrame.ofClean state.clean state.world) (localWordCells ctx state.values)

def run {ctx : Solidity.Source.Ctx} (name : String) (value : Bool)
    (fuel : Nat) (state : RawFrame.State ctx) :
    Sum (Solidity.Source.Halt × RawFrame.State ctx)
      (RawFrame.State (ctx.push name .bool)) :=
  RawDefaultDeclaration.Result.casesOn (motive := fun _ =>
    Sum (Solidity.Source.Halt × RawFrame.State ctx)
      (RawFrame.State (ctx.push name .bool)))
    (RawLiteralInitialization.run value fuel (RawLocalDeclaration.Snapshot.ofFrame state))
    (fun next => .inr (ofSnapshot (ctx := ctx.push name .bool) next))
    (fun halt _previous => .inl (halt,state))

def project {ctx : Solidity.Source.Ctx} {name : String}
    (result : Sum (Solidity.Source.Halt × RawFrame.State ctx)
      (RawFrame.State (ctx.push name .bool))) :
    Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys (.bool :: ctx.tys)) ×
      (Solidity.Source.Locals ctx.env.layout [] × Solidity.Source.St ctx.env) :=
  match result with
  | .inl failure => (.error failure.1,(Solidity.Source.L0 ctx.env,failure.2.world))
  | .inr next => (.ok (.normal next.clean),(Solidity.Source.L0 ctx.env,next.world))

end Solidity.Yul.RawDeclarationFrame

namespace Solidity.Yul.RawDeclarationFrame
theorem view_snapshot : ∀ (ctx : Solidity.Source.Ctx) (state : Solidity.Yul.RawLocalDeclaration.Snapshot ctx.env ctx.tys), Solidity.Yul.RawFrame.view (Solidity.Yul.RawDeclarationFrame.ofSnapshot state) = Solidity.Yul.localWordCells ctx state.values := by
  intro ctx state
  rfl

theorem clean_snapshot : ∀ (ctx : Solidity.Source.Ctx) (state : Solidity.Yul.RawLocalDeclaration.Snapshot ctx.env ctx.tys), (Solidity.Yul.RawDeclarationFrame.ofSnapshot state).clean = state.clean := by
  intro ctx state
  rfl

theorem world_snapshot : ∀ (ctx : Solidity.Source.Ctx) (state : Solidity.Yul.RawLocalDeclaration.Snapshot ctx.env ctx.tys), (Solidity.Yul.RawDeclarationFrame.ofSnapshot state).world = state.world := by
  intro ctx state
  rfl

theorem frame_roundtrip : ∀ (ctx : Solidity.Source.Ctx) (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawFrame.view (Solidity.Yul.RawDeclarationFrame.ofSnapshot (Solidity.Yul.RawLocalDeclaration.Snapshot.ofFrame state)) = Solidity.Yul.RawFrame.view state := by
  intro ctx state
  exact RawFrame.materialize_view state

theorem coherent_iff : ∀ (ctx : Solidity.Source.Ctx) (state : Solidity.Yul.RawLocalDeclaration.Snapshot ctx.env ctx.tys), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawDeclarationFrame.ofSnapshot state) = true ↔ Solidity.Yul.localWordCells ctx state.values = Solidity.Yul.localWordCells ctx (Solidity.Yul.LocalValues.ofClean state.clean) := by
  intro ctx state
  exact RawCoherent.coherent_iff (ofSnapshot state)

theorem run_zero : ∀ (ctx : Solidity.Source.Ctx) (name : String) (value : Bool) (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawDeclarationFrame.run name value 0 state = .inl (.timeout,state) := by
  intro ctx name value state
  rfl

theorem run_one : ∀ (ctx : Solidity.Source.Ctx) (name : String) (value : Bool) (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawDeclarationFrame.run name value 1 state = .inl (.timeout,state) := by
  intro ctx name value state
  rfl

theorem run_success : ∀ (ctx : Solidity.Source.Ctx) (name : String) (value : Bool) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawDeclarationFrame.run name value (fuel+2) state = .inr
 (Solidity.Yul.RawDeclarationFrame.ofSnapshot (ctx := ctx.push name .bool)
  ⟨.cons (.bool value) state.clean,(.clean (.bool value),(Solidity.Yul.RawFrame.materialize state).1),state.world⟩) := by
  intro ctx name value fuel state
  rfl

theorem source_correct : ∀ (ctx : Solidity.Source.Ctx) (name : String) (value : Bool)
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Source.execS glob frame fuel nps ph
 (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
 (k := control) (Γ := ctx.tys) (τ := .bool) (.bool value) (by rfl)) state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawDeclarationFrame.project (Solidity.Yul.RawDeclarationFrame.run name value fuel state) := by
  intro ctx name value returns modifier control glob frame fuel nps ph state
  cases fuel with
  | zero => rfl
  | succ fuel => cases fuel <;> rfl

end Solidity.Yul.RawDeclarationFrame
