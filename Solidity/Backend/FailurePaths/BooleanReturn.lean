import Solidity.Backend.FailurePaths.Returns

/-!
# Literal Boolean return statements

A body with one Boolean return slot, no parameters or additional locals, is
compiled at its ABI return boundary. Source.execS, retVals and encodeVals are
all the existing upstream operations. General return expressions, other return
signatures, internal-frame conventions and world/EVM adequacy remain separate.
-/
namespace Solidity.Backend.FailurePaths.BooleanReturn
open Source

def statement {E : Source.Env} {Γ : RCtx} (value : Bool) :
    RStmt E [.bool] false .body Γ Γ :=
  .retVal rfl (.bool value) rfl

def locals {E : Source.Env} (value : Bool) : Locals E.layout [.bool] :=
  .cons (.bool value) .nil

def values {E : Source.Env} (value : Bool) : RVals E.layout [.bool] :=
  .cons (.val (.bool value)) .nil

def payload (value : Bool) : Roadmap.Bytes :=
  Lowering.V08.BoolErrorLowering.encoded [value]

/-- A certificate over the existing indexed statement, not another term IR. -/
structure View {E : Source.Env} {Γ Δ : RCtx} (stmt : RStmt E [.bool] false .body Γ Δ) where
  value : Bool
  contexts : Δ = Γ
  same : HEq stmt (statement (E := E) (Γ := Γ) value)

def view {E : Source.Env} {Γ Δ : RCtx} : (stmt : RStmt E [.bool] false .body Γ Δ) → Option (View stmt)
  | .retVal (τ := τ) result expr _ =>
      match found : Lowering.V08.LiteralFailureLowering.boolLiteral expr with
      | none => none
      | some value => some ⟨value, rfl, by
          have target : STy.bool = τ := (List.cons.inj result).1
          obtain ⟨sourceType, sameExpr⟩ :=
            Lowering.V08.LiteralFailureLowering.boolLiteral_inv expr value found
          cases target
          cases sourceType
          cases sameExpr
          rfl⟩
  | _ => none

def compile {E : Source.Env} (offset : Nat)
    (stmt : RStmt E [.bool] false .body [.bool] [.bool]) : Option Backend.Program :=
  (view stmt).map fun selected => Failure.emit offset (.returned (payload selected.value))

/-- The old hidden return slot is actually overwritten, and all source state
fields remain unchanged. This is not an assumed function-return result. -/
theorem source_run {E : Source.Env} (global : Glob E) (frame : Fr) (extra : Nat)
    (old value : Bool) (state : St E) :
    (execS global frame (extra + 7) 0 none (statement value) (locals old)).run (Source.L0 E, state) =
      (.ok (.ret (locals value)), (Source.L0 E, state)) := rfl

theorem returned_values {E : Source.Env} (value : Bool) :
    retVals (locals (E := E) value) 0 [.bool] = .ok (values value) := rfl

theorem encoded_values {E : Source.Env} (frame : Fr) (fuel : Nat) (value : Bool) (state : St E) :
    (encodeVals frame fuel false (values value) : EM E [] _).run (Source.L0 E, state) =
      (.ok (payload value), (Source.L0 E, state)) :=
  Lowering.V08.BoolErrorLowering.encoding_run frame fuel [value] (Source.L0 E) state

/-- Every accepted actual return statement has a source return-slot result,
actual return-value extraction and encoding, and exact target RETURN bytes.
Fits/stack remain the published target gates in Emits. -/
theorem selected_correct {E : Source.Env} (global : Glob E) (frame : Fr) (extra offset : Nat)
    (stmt : RStmt E [.bool] false .body [.bool] [.bool]) (code : Backend.Program)
    (selected : compile offset stmt = some code) (old : Bool) (state : St E) :
    ∃ value,
      (execS global frame (extra + 7) 0 none stmt (locals old)).run (Source.L0 E, state) =
        (.ok (.ret (locals value)), (Source.L0 E, state)) ∧
      retVals (locals (E := E) value) 0 [.bool] = .ok (values value) ∧
      (encodeVals frame extra false (values value) : EM E [] _).run (Source.L0 E, state) =
        (.ok (payload value), (Source.L0 E, state)) ∧
      Emits code offset (.returned (payload value)) := by
  cases found : view stmt with
  | none => simp only [compile, found, Option.map_none, reduceCtorEq] at selected
  | some witness =>
    obtain ⟨value, _, same⟩ := witness
    simp only [compile, found, Option.map_some, Option.some.injEq] at selected
    subst code
    refine ⟨value, ?_, returned_values value,
      encoded_values frame extra value state, Failure.checkedRun_emit_suffix offset _⟩
    have syntaxEq : stmt = statement value := eq_of_heq same
    rw [syntaxEq]
    exact source_run global frame extra old value state

#print axioms source_run
#print axioms returned_values
#print axioms encoded_values
#print axioms selected_correct
end Solidity.Backend.FailurePaths.BooleanReturn
