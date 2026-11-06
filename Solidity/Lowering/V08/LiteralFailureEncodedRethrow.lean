import Solidity.Lowering.V08.LiteralFailureSelectorBytes
import Solidity.Lowering.V08.SourceRethrow

namespace Solidity.Lowering.V08.LiteralFailureEncodedRethrow
open Solidity Source LiteralFailureDynamicListError

theorem selector_rethrow {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra statementFuel : Nat)
 (selector : Source.Idx Γ LiteralFailureSelectorBytes.Selector)
 (refs : List (Source.Idx Γ (.bytes .memory))) (packets : List Roadmap.Bytes)
 (locals : Locals E.layout Γ) (state : St E) (memory : all_represented locals state refs packets) :
 (SourceRethrow.fromExpression G F (refs.length+extra+5) (statementFuel+1)
  (.abiEncode .encodeWithSelector (LiteralFailureSelectorBytes.args selector refs))).run (locals,state) =
 (.error (.revert ((locals.get selector).bytesOf ++ AbiEntry.encodeArgs (abiValues packets))),
  (locals,SourceKeccak.afterLiteral state
   ((locals.get selector).bytesOf ++ AbiEntry.encodeArgs (abiValues packets)))) := by
 exact SourceRethrow.expression_rethrow G F (refs.length+extra+5) statementFuel
  (.abiEncode .encodeWithSelector (LiteralFailureSelectorBytes.args selector refs))
  locals locals state _ state.heap.next _
  (LiteralFailureSelectorBytes.expression_run G F extra selector refs packets locals state memory)
  (SourceKeccak.allocated state _)

theorem signature_rethrow {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra statementFuel : Nat)
 (signature : Source.Idx Γ (.bytes .memory))
 (refs : List (Source.Idx Γ (.bytes .memory))) (text : Roadmap.Bytes)
 (packets : List Roadmap.Bytes) (locals : Locals E.layout Γ) (state : St E)
 (sigMemory : represented locals state signature text)
 (memory : all_represented locals state refs packets) :
 (SourceRethrow.fromExpression G F (refs.length+extra+5) (statementFuel+1)
  (.abiEncode .encodeWithSignature (LiteralFailurePackedBytes.args (signature::refs)))).run (locals,state) =
 (.error (.revert ((wordBytes (G.fixed.hash text)).take 4 ++ AbiEntry.encodeArgs (abiValues packets))),
  (locals,SourceKeccak.afterLiteral state
   ((wordBytes (G.fixed.hash text)).take 4 ++ AbiEntry.encodeArgs (abiValues packets)))) := by
 exact SourceRethrow.expression_rethrow G F (refs.length+extra+5) statementFuel
  (.abiEncode .encodeWithSignature (LiteralFailurePackedBytes.args (signature::refs)))
  locals locals state _ state.heap.next _
  (LiteralFailureSignatureBytes.expression_run G F extra signature refs text packets locals state sigMemory memory)
  (SourceKeccak.allocated state _)

theorem packed_rethrow {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra statementFuel : Nat)
 (refs : List (Source.Idx Γ (.bytes .memory))) (packets : List Roadmap.Bytes)
 (locals : Locals E.layout Γ) (state : St E) (memory : all_represented locals state refs packets) :
 (SourceRethrow.fromExpression G F (refs.length+extra+4) (statementFuel+1)
  (.abiEncode .encodePacked (LiteralFailurePackedBytes.args refs))).run (locals,state) =
 (.error (.revert packets.flatten),(locals,SourceKeccak.afterLiteral state packets.flatten)) := by
 exact SourceRethrow.expression_rethrow G F (refs.length+extra+4) statementFuel
  (.abiEncode .encodePacked (LiteralFailurePackedBytes.args refs)) locals locals state _ state.heap.next _
  (LiteralFailurePackedBytes.expression_run G F extra refs packets locals state memory)
  (SourceKeccak.allocated state _)

theorem selector_statement_timeout {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra : Nat)
 (selector : Source.Idx Γ LiteralFailureSelectorBytes.Selector)
 (refs : List (Source.Idx Γ (.bytes .memory))) (packets : List Roadmap.Bytes)
 (locals : Locals E.layout Γ) (state : St E) (memory : all_represented locals state refs packets) :
 (SourceRethrow.fromExpression G F (refs.length+extra+5) 0
  (.abiEncode .encodeWithSelector (LiteralFailureSelectorBytes.args selector refs))).run (locals,state) =
 (.error .timeout,(locals,SourceKeccak.afterLiteral state
  ((locals.get selector).bytesOf ++ AbiEntry.encodeArgs (abiValues packets)))) := by
 have expression := LiteralFailureSelectorBytes.expression_run G F extra selector refs packets locals state memory
 have statement := SourceCustomErrorFailures.rethrow_zero_horizon G F
  (Source.Idx.here : Source.Idx [.bytes .memory] (.bytes .memory))
  (.cons (.memRef rfl state.heap.next) .nil)
  (SourceKeccak.afterLiteral state ((locals.get selector).bytesOf ++ AbiEntry.encodeArgs (abiValues packets)))
 simp only [ExceptT.run] at expression statement
 simp only [SourceRethrow.fromExpression,EM.sub,getV,RVal.get,EM.lift,
  bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
  StateT.bind,StateT.pure,Except.pure,expression,statement]

theorem selector_expression_timeout {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (statementHorizon : Nat)
 (selector : Source.Idx Γ LiteralFailureSelectorBytes.Selector)
 (refs : List (Source.Idx Γ (.bytes .memory))) (locals : Locals E.layout Γ) (state : St E) :
 (SourceRethrow.fromExpression G F 0 statementHorizon
  (.abiEncode .encodeWithSelector (LiteralFailureSelectorBytes.args selector refs))).run (locals,state) =
 (.error .timeout,(locals,state)) :=
 SourceRethrow.expression_failure G F 0 statementHorizon
  (.abiEncode .encodeWithSelector (LiteralFailureSelectorBytes.args selector refs))
  locals locals state state .timeout rfl

end Solidity.Lowering.V08.LiteralFailureEncodedRethrow
