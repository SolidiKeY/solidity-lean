import Solidity.Yul.RawDeclarationFrame

/-! Concrete literal declaration adapter using existing exact-word preparation.
Coherent inputs retain their actual clean constructors; dirty inputs retain
materialized words. No bits are truncated, no ordinary dirty read is inferred,
and the existing materialized declaration runner remains unchanged. -/
namespace Solidity.Yul.RawPreparedDeclaration

def input {ctx : Solidity.Source.Ctx} (state : RawFrame.State ctx) :
    RawLocalDeclaration.Snapshot ctx.env ctx.tys :=
  ⟨state.clean,(RawCoherent.prepare state).1,state.world⟩

def run {ctx : Solidity.Source.Ctx} (name : String) (value : Bool)
    (fuel : Nat) (state : RawFrame.State ctx) :
    Sum (Solidity.Source.Halt × RawFrame.State ctx)
      (RawFrame.State (ctx.push name .bool)) :=
  RawDefaultDeclaration.Result.casesOn (motive := fun _ =>
    Sum (Solidity.Source.Halt × RawFrame.State ctx)
      (RawFrame.State (ctx.push name .bool)))
    (RawLiteralInitialization.run value fuel (input state))
    (fun next => .inr (RawDeclarationFrame.ofSnapshot (ctx := ctx.push name .bool) next))
    (fun halt _previous => .inl (halt,state))

end Solidity.Yul.RawPreparedDeclaration

namespace Solidity.Yul.RawPreparedDeclaration
theorem input_words : ∀ (ctx : Solidity.Source.Ctx) (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.localWordCells ctx (Solidity.Yul.RawPreparedDeclaration.input state).values = Solidity.Yul.RawFrame.view state := by
  intro ctx state
  exact RawCoherent.prepare_view state

theorem run_zero : ∀ (ctx : Solidity.Source.Ctx) (name : String) (value : Bool) (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawPreparedDeclaration.run name value 0 state = .inl (.timeout,state) := by
  intro ctx name value state
  rfl

theorem run_one : ∀ (ctx : Solidity.Source.Ctx) (name : String) (value : Bool) (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawPreparedDeclaration.run name value 1 state = .inl (.timeout,state) := by
  intro ctx name value state
  rfl

theorem run_success : ∀ (ctx : Solidity.Source.Ctx) (name : String) (value : Bool) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawPreparedDeclaration.run name value (fuel+2) state = .inr
 (Solidity.Yul.RawDeclarationFrame.ofSnapshot (ctx := ctx.push name .bool)
  ⟨.cons (.bool value) state.clean,(.clean (.bool value),(Solidity.Yul.RawCoherent.prepare state).1),state.world⟩) := by
  intro ctx name value fuel state
  rfl

theorem coherent_result : ∀ (ctx : Solidity.Source.Ctx) (name : String) (value : Bool) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawCoherent.coherent state = true → match Solidity.Yul.RawPreparedDeclaration.run name value fuel state with
 | .inl failure => Solidity.Yul.RawCoherent.coherent failure.2 = true
 | .inr next => Solidity.Yul.RawCoherent.coherent next = true := by
  intro ctx name value fuel state same
  cases fuel with
  | zero => exact same
  | succ fuel =>
    cases fuel with
    | zero => exact same
    | succ fuel =>
      change RawCoherent.coherent
        (RawDeclarationFrame.ofSnapshot (ctx := ctx.push name .bool)
          ⟨.cons (.bool value) state.clean,(.clean (.bool value),(RawCoherent.prepare state).1),state.world⟩) = true
      rw [RawCoherent.prepare_coherent state same]
      exact (RawCoherent.coherent_iff _).mpr rfl

theorem source_correct : ∀ (ctx : Solidity.Source.Ctx) (name : String) (value : Bool)
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Source.execS glob frame fuel nps ph
 (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
 (k := control) (Γ := ctx.tys) (τ := .bool) (.bool value) (by rfl)) state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawDeclarationFrame.project (Solidity.Yul.RawPreparedDeclaration.run name value fuel state) := by
  intro ctx name value returns modifier control glob frame fuel nps ph state
  cases fuel with
  | zero => rfl
  | succ fuel => cases fuel <;> rfl

theorem dirty_agrees : ∀ (ctx : Solidity.Source.Ctx) (name : String) (value : Bool) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawCoherent.coherent state ≠ true →
 Solidity.Yul.RawPreparedDeclaration.run name value fuel state = Solidity.Yul.RawDeclarationFrame.run name value fuel state := by
  intro ctx name value fuel state dirty
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      have prepared : RawCoherent.prepare state = RawFrame.materialize state := by
        unfold RawCoherent.prepare
        rw [if_neg dirty]
      change Sum.inr
        (RawDeclarationFrame.ofSnapshot (ctx := ctx.push name .bool)
          ⟨.cons (.bool value) state.clean,(.clean (.bool value),(RawCoherent.prepare state).1),state.world⟩) =
        Sum.inr (RawDeclarationFrame.ofSnapshot (ctx := ctx.push name .bool)
          ⟨.cons (.bool value) state.clean,(.clean (.bool value),(RawFrame.materialize state).1),state.world⟩)
      rw [prepared]

end Solidity.Yul.RawPreparedDeclaration
