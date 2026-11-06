import Solidity.Lowering.V08.SourceEnvironment
import Solidity.Lowering.V08.AbiObservations

/-!
# Literal reason failures from independent source execution

The lowering clause uses existing intrinsic RevPart.bytes/revertData and the
published encoders; it adds no decoder or failure emitter. It proves execution
of the supplied typed constructors, not that a production compiler selects them.
Arbitrary argument effects, admission, frame rollback and bytecode remain separate.
-/
namespace Solidity.Lowering.V08.SourceFailures
open Solidity
open Source

def reason {E : Source.Env} {Γ : RCtx} (bytes : Roadmap.Bytes) : RExpr E Γ (.tuple []) :=
  .builtin .revert (.cons (.str bytes) .nil) rfl

/-- A sufficient horizon for this finite syntax, not an admission depth bound.
The literal path allocates nothing and retains the entire actual source state. -/
theorem eval_reason {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (bytes : Roadmap.Bytes) (locals : Source.Locals E.layout Γ)
    (state : Source.St E) :
    (Source.evalE global frame (horizon + 5) (reason bytes)).run (locals, state) =
      (.error (.revert (Source.errorData bytes)), (locals, state)) := rfl

theorem eval_reason_transport {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (bytes : Roadmap.Bytes) (locals : Source.Locals E.layout Γ)
    (state : Source.St E) :
    (Source.evalE global frame (horizon + 5) (reason bytes)).run (locals, state) =
      (.error (.revert (Semantics.encodeError bytes)), (locals, state)) := by
  rw [eval_reason, errorData_transport_total]

/-- An insufficient horizon is exactly timeout, never the completed revert. -/
theorem reason_low_horizon {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (bytes : Roadmap.Bytes) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.evalE global frame 2 (reason bytes)).run (locals, state) =
      (.error .timeout, (locals, state)) := rfl

def reasonStatement {C : Contract} {Δ : Ctx} (bytes : Roadmap.Bytes) : Stmt C Δ Δ :=
  .revertData [.bytes (Semantics.encodeError bytes)]

/-- Actual execution of the existing typed revert constructor. No state is
returned by this error, so this alone makes no rollback claim. -/
theorem target_reason {C : Contract} {Δ : Ctx} (bytes : Roadmap.Bytes) (state : State C Δ) :
    (reasonStatement bytes).runC state =
      .error (.revertWith (Semantics.encodeError bytes)) := by
  simp only [reasonStatement, Stmt.runC, TRun.revertData, List.mapM_cons,
    List.mapM_nil, RevPart.evalT]
  change Except.error (THalt.ofData (Semantics.encodeError bytes ++ [])) = _
  rw [List.append_nil]
  rfl

theorem reason_execution_transport {E : Source.Env} {Γ : RCtx} {C : Contract} {Δ : Ctx}
    (global : Glob E) (frame : Fr) (horizon : Nat) (bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (source : Source.St E) (target : State C Δ) :
    (Source.evalE global frame (horizon + 5) (reason bytes)).run (locals, source) =
      (.error (.revert (Semantics.encodeError bytes)), (locals, source)) ∧
    (reasonStatement bytes).runC target =
      .error (.revertWith (Semantics.encodeError bytes)) :=
  ⟨eval_reason_transport global frame horizon bytes locals source, target_reason bytes target⟩

theorem exec_reason {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (bytes : Roadmap.Bytes) (locals : Source.Locals E.layout Γ)
    (state : Source.St E) :
    (Source.execS global frame (horizon + 6) 0 none
      (.expr (reason bytes) : RStmt E [] false .body Γ Γ) locals).run
        (Source.L0 E, state) =
      (.error (.revert (Source.errorData bytes)), (Source.L0 E, state)) := rfl

#print axioms eval_reason
#print axioms eval_reason_transport
#print axioms reason_low_horizon
#print axioms target_reason
#print axioms reason_execution_transport
#print axioms exec_reason
end Solidity.Lowering.V08.SourceFailures
