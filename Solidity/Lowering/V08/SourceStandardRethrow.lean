import Solidity.Lowering.V08.SourceRethrow

/-! Actual standard ABI allocation followed by canonical Source rethrow.
Existing producers are consumed. No new evaluator, encoder, admission bound,
compiler selection or catch/frame/bytecode adequacy is introduced. -/
namespace Solidity.Lowering.V08.SourceStandardRethrow
open Solidity Source

def literal {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (allocationHorizon statementHorizon : Nat) (bytes : Roadmap.Bytes) :
    Source.EM E Γ (Source.Out E.layout [.bytes .memory] [.bytes .memory] × Source.Locals E.layout []) :=
  SourceRethrow.fromExpression (Γ:=Γ) global frame allocationHorizon statementHorizon
    (SourceAbi.literal false bytes)

theorem literal_execution {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (allocationFuel statementFuel : Nat) (bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (literal global frame (allocationFuel+4) (statementFuel+1) bytes).run (locals,state) =
      (.error (.revert (Source.abiLayout [(true,bytes)])),
        (locals,SourceKeccak.afterLiteral state (Source.abiLayout [(true,bytes)]))) :=
  SourceRethrow.expression_rethrow global frame (allocationFuel+4) statementFuel
    (SourceAbi.literal false bytes) locals locals state _ state.heap.next _
    (SourceAbi.literal_execution global frame allocationFuel false bytes locals state)
    (SourceRethrow.allocated_object state (Source.abiLayout [(true,bytes)]))

/-- The statement horizon ends AFTER the actual expression's reached effects;
its zero-horizon branch does not read memory or undo the expression. -/
theorem expression_statement_timeout {E : Source.Env} {Γ : RCtx}
    (global : Glob E) (frame : Fr) (expressionHorizon : Nat)
    (expression : RExpr E Γ (.bytes .memory)) (locals reached : Source.Locals E.layout Γ)
    (state final : Source.St E) (address : Nat)
    (evaluation : (Source.evalE global frame expressionHorizon expression).run (locals,state) =
      (.ok (.val (.memRef rfl address)),(reached,final))) :
    (SourceRethrow.fromExpression global frame expressionHorizon 0 expression).run (locals,state) =
      (.error .timeout,(reached,final)) := by
  have statement := SourceCustomErrorFailures.rethrow_zero_horizon global frame
    (Source.Idx.here : Source.Idx [.bytes .memory] (.bytes .memory))
    (.cons (.memRef rfl address) .nil) final
  simp only [ExceptT.run] at evaluation statement
  simp only [SourceRethrow.fromExpression,Source.EM.sub,Source.getV,Source.RVal.get,Source.EM.lift,
    bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,Except.pure,evaluation,statement]

theorem literal_statement_timeout {E : Source.Env} {Γ : RCtx}
    (global : Glob E) (frame : Fr) (allocationFuel : Nat) (bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (literal global frame (allocationFuel+4) 0 bytes).run (locals,state) =
      (.error .timeout,(locals,SourceKeccak.afterLiteral state (Source.abiLayout [(true,bytes)]))) :=
  expression_statement_timeout global frame (allocationFuel+4) (SourceAbi.literal false bytes)
    locals locals state _ state.heap.next
    (SourceAbi.literal_execution global frame allocationFuel false bytes locals state)

theorem literal_allocation_timeout {E : Source.Env} {Γ : RCtx}
    (global : Glob E) (frame : Fr) (statementHorizon : Nat) (bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (literal global frame 0 statementHorizon bytes).run (locals,state) =
      (.error .timeout,(locals,state)) :=
  SourceRethrow.expression_failure global frame 0 statementHorizon (SourceAbi.literal false bytes)
    locals locals state state .timeout (SourceAbi.zero_horizon global frame false bytes locals state)

theorem literal_argument_timeout {E : Source.Env} {Γ : RCtx}
    (global : Glob E) (frame : Fr) (statementHorizon : Nat) (bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (literal global frame 1 statementHorizon bytes).run (locals,state) =
      (.error .timeout,(locals,state)) :=
  SourceRethrow.expression_failure global frame 1 statementHorizon (SourceAbi.literal false bytes)
    locals locals state state .timeout (SourceAbi.argument_horizon_zero global frame false bytes locals state)

/-- Existing intrinsic word/padding projection of precisely the executed data.
This is neither Error(string) wrapping nor another payload emitter. -/
theorem literal_bytes_transport {E : Source.Env} {Γ : RCtx}
    (global : Glob E) (frame : Fr) (allocationFuel statementFuel : Nat) (bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (literal global frame (allocationFuel+4) (statementFuel+1) bytes).run (locals,state) =
      (.error (.revert (Semantics.wordBytes 32 ++
        (Semantics.wordBytes bytes.length ++ Semantics.pad32 bytes))),
       (locals,SourceKeccak.afterLiteral state (Semantics.wordBytes 32 ++
        (Semantics.wordBytes bytes.length ++ Semantics.pad32 bytes)))) := by
  simpa only [SourceAbi.single_dynamic_bytes] using
    literal_execution global frame allocationFuel statementFuel bytes locals state

theorem execution_transport {E : Source.Env} {Γ : RCtx} {C : Contract} {Δ : Ctx}
    (global : Glob E) (frame : Fr) (allocationFuel statementFuel : Nat) (bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (source : Source.St E) (target : State C Δ) :
    (literal global frame (allocationFuel+4) (statementFuel+1) bytes).run (locals,source) =
      (.error (.revert (Source.abiLayout [(true,bytes)])),
       (locals,SourceKeccak.afterLiteral source (Source.abiLayout [(true,bytes)]))) ∧
    (Stmt.revertData [.bytes (Source.abiLayout [(true,bytes)])] : Stmt C Δ Δ).runC target =
      .error (THalt.ofData (Source.abiLayout [(true,bytes)])) :=
  ⟨literal_execution global frame allocationFuel statementFuel bytes locals source,
    SourceRethrow.intrinsic_rethrow _ target⟩

#print axioms literal_execution
#print axioms expression_statement_timeout
#print axioms literal_statement_timeout
#print axioms literal_allocation_timeout
#print axioms literal_argument_timeout
#print axioms literal_bytes_transport
#print axioms execution_transport
end Solidity.Lowering.V08.SourceStandardRethrow
