import Solidity.Lowering.V08.SourceAbi
import Solidity.Lowering.V08.SourceCustomErrorFailures

/-! Composition of actual independent Source allocation and its canonical rethrow.
The primitive rethrow law is consumed from SourceCustomErrorFailures; this file
adds the reached-reference application, not another evaluator or payload emitter.
The source retains its allocated heap on error. Intrinsic error execution returns
no world; no rollback or compiler/body/layout/catch selection is inferred. -/
namespace Solidity.Lowering.V08.SourceRethrow
open Solidity Source

/-- Ordinary composition through the published EM/getV/sub operations. -/
def allocated {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (allocationHorizon rethrowHorizon : Nat) (bytes : Roadmap.Bytes) :
    Source.EM E Γ (Source.Out E.layout [.bytes .memory] [.bytes .memory] × Source.Locals E.layout []) := do
  let reference ← Source.getV (← Source.evalE global frame allocationHorizon (SourceAbi.literal true bytes))
  Source.EM.sub (Source.L0 E) (Source.execS global frame rethrowHorizon 0 none
    (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
    (.cons reference .nil))

theorem allocated_object {E : Source.Env} (state : Source.St E) (bytes : Roadmap.Bytes) :
    (SourceKeccak.afterLiteral state bytes).heap.get state.heap.next =
      some ⟨.bytes .memory,.bytes bytes⟩ :=
  Source.Heap.alloc_get state.heap ⟨.bytes .memory,.bytes bytes⟩

/-- The local passed to execS is exactly the reference returned by allocation. -/
theorem reached_rethrow {E : Source.Env} (global : Glob E) (frame : Fr)
    (horizon : Nat) (state : Source.St E) (bytes : Roadmap.Bytes) :
    (Source.execS global frame (horizon+1) 0 none
      (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
      (.cons (.memRef rfl state.heap.next) .nil)).run
        (Source.L0 E,SourceKeccak.afterLiteral state bytes) =
      (.error (.revert bytes),(Source.L0 E,SourceKeccak.afterLiteral state bytes)) :=
  SourceCustomErrorFailures.rethrow_bytes global frame horizon .here _ _ state.heap.next bytes
    rfl (allocated_object state bytes)

theorem literal_rethrow {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (allocationFuel statementFuel : Nat) (bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (allocated global frame (allocationFuel+4) (statementFuel+1) bytes).run (locals,state) =
      (.error (.revert bytes),(locals,SourceKeccak.afterLiteral state bytes)) := by
  have expression := SourceAbi.literal_execution global frame allocationFuel true bytes locals state
  have statement := reached_rethrow global frame statementFuel state bytes
  simp only [ExceptT.run] at expression statement
  simp only [allocated,Source.EM.sub,Source.getV,Source.RVal.get,Source.EM.lift,
    bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,Except.pure,↓reduceIte,expression,statement]

/-- Allocation still occurred when only the statement horizon is insufficient. -/
theorem statement_timeout {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (allocationFuel : Nat) (bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (allocated global frame (allocationFuel+4) 0 bytes).run (locals,state) =
      (.error .timeout,(locals,SourceKeccak.afterLiteral state bytes)) := by
  have expression := SourceAbi.literal_execution global frame allocationFuel true bytes locals state
  have statement := SourceCustomErrorFailures.rethrow_zero_horizon global frame
    (Source.Idx.here : Source.Idx [.bytes .memory] (.bytes .memory))
    (.cons (.memRef rfl state.heap.next) .nil) (SourceKeccak.afterLiteral state bytes)
  simp only [ExceptT.run] at expression statement
  simp only [allocated,Source.EM.sub,Source.getV,Source.RVal.get,Source.EM.lift,
    bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,Except.pure,↓reduceIte,expression,statement]

theorem allocation_timeout {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (statementFuel : Nat) (bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (allocated global frame 0 statementFuel bytes).run (locals,state) =
      (.error .timeout,(locals,state)) := rfl

/-- Existing typed revert constructor, independently supplied. Its empty-data
halt is revert; nonempty data is revertWith, with no error-payload wrapping. -/
theorem intrinsic_rethrow {C : Contract} {Δ : Ctx} (bytes : Roadmap.Bytes) (state : State C Δ) :
    (Stmt.revertData [.bytes bytes] : Stmt C Δ Δ).runC state =
      .error (THalt.ofData bytes) := by
  simp only [Stmt.runC,TRun.revertData,List.mapM_cons,List.mapM_nil,RevPart.evalT]
  change Except.error (THalt.ofData (bytes ++ [])) = _
  rw [List.append_nil]

/-- Two actual executions and exact byte observation; no premise says the
compiler selects this intrinsic statement or relates their memory frames. -/
theorem execution_transport {E : Source.Env} {Γ : RCtx} {C : Contract} {Δ : Ctx}
    (global : Glob E) (frame : Fr) (allocationFuel statementFuel : Nat) (bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (source : Source.St E) (target : State C Δ) :
    (allocated global frame (allocationFuel+4) (statementFuel+1) bytes).run (locals,source) =
      (.error (.revert bytes),(locals,SourceKeccak.afterLiteral source bytes)) ∧
    (Stmt.revertData [.bytes bytes] : Stmt C Δ Δ).runC target = .error (THalt.ofData bytes) :=
  ⟨literal_rethrow global frame allocationFuel statementFuel bytes locals source,
    intrinsic_rethrow bytes target⟩

/-- The same published boundary for any bytes-memory expression. The execution
and heap premises are individual independent Source steps, not compiler adequacy. -/
def fromExpression {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (expressionHorizon rethrowHorizon : Nat) (expression : RExpr E Γ (.bytes .memory)) :
    Source.EM E Γ (Source.Out E.layout [.bytes .memory] [.bytes .memory] × Source.Locals E.layout []) := do
  let reference ← Source.getV (← Source.evalE global frame expressionHorizon expression)
  Source.EM.sub (Source.L0 E) (Source.execS global frame rethrowHorizon 0 none
    (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
    (.cons reference .nil))

theorem expression_rethrow {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (expressionHorizon statementFuel : Nat) (expression : RExpr E Γ (.bytes .memory))
    (locals reached : Source.Locals E.layout Γ) (state final : Source.St E)
    (address : Nat) (bytes : Roadmap.Bytes)
    (evaluation : (Source.evalE global frame expressionHorizon expression).run (locals,state) =
      (.ok (.val (.memRef rfl address)),(reached,final)))
    (memory : final.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (fromExpression global frame expressionHorizon (statementFuel+1) expression).run (locals,state) =
      (.error (.revert bytes),(reached,final)) := by
  have statement := SourceCustomErrorFailures.rethrow_bytes global frame statementFuel
    (Source.Idx.here : Source.Idx [.bytes .memory] (.bytes .memory))
    (.cons (.memRef rfl address) .nil) final address bytes rfl memory
  simp only [ExceptT.run] at evaluation statement
  simp only [fromExpression,Source.EM.sub,Source.getV,Source.RVal.get,Source.EM.lift,
    bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,Except.pure,evaluation,statement]

/-- A real expression failure prevents the later rethrow and retains the exact
already-reached locals/state, even if argument effects preceded the failure. -/
theorem expression_failure {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (expressionHorizon statementHorizon : Nat) (expression : RExpr E Γ (.bytes .memory))
    (locals reached : Source.Locals E.layout Γ) (state final : Source.St E) (halt : Source.Halt)
    (evaluation : (Source.evalE global frame expressionHorizon expression).run (locals,state) =
      (.error halt,(reached,final))) :
    (fromExpression global frame expressionHorizon statementHorizon expression).run (locals,state) =
      (.error halt,(reached,final)) := by
  simp only [ExceptT.run] at evaluation
  simp only [fromExpression,bind,pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,evaluation]

#print axioms expression_rethrow
#print axioms expression_failure

#print axioms allocated_object
#print axioms reached_rethrow
#print axioms literal_rethrow
#print axioms statement_timeout
#print axioms allocation_timeout
#print axioms intrinsic_rethrow
#print axioms execution_transport
end Solidity.Lowering.V08.SourceRethrow
