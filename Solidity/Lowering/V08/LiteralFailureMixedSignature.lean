import Solidity.Lowering.V08.LiteralFailureMixedExpression
import Solidity.Lowering.V08.LiteralFailureSignatureBytes

/-! Actual encodeWithSignature for heterogeneous local arguments. This consumes
published lookup, signature-memory reads, hashing, codec and allocation semantics;
no dispatch or same-invocation/target correspondence is assumed. -/
namespace Solidity.Lowering.V08.LiteralFailureMixedSignature
open Solidity Source
open LiteralFailureMixedExpression (LocalArgs)

theorem arguments_run {E : Env} {Γ types} {arguments : RArgs E Γ types}
 {values : Source.Vals E.layout types} (G : Glob E) (F : Fr) (extra : Nat)
 (index : Source.Idx Γ (.bytes .memory)) (locals : Locals E.layout Γ) (state : St E)
 (lookups : LocalArgs locals arguments values) :
 (evalArgs G F (types.length+extra+4) (.cons (.local index) arguments)).run (locals,state)=
 (.ok (.cons (.val (locals.get index)) values.toR),(locals,state)) := by
 rw [evalArgs]
 simp only [evalE,EM.locals,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
  ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,get,getThe,
  MonadStateOf.get,liftM,monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map]
 have tail := LiteralFailureMixedExpression.arguments_run G F extra locals state lookups
 dsimp only [ExceptT.run] at tail
 rw [tail]
 rfl

theorem expression_run {E : Env} {Γ types shapes} {arguments : RArgs E Γ types}
 {values : Source.Vals E.layout types} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra : Nat) (index : Source.Idx Γ (.bytes .memory))
 (locals : Locals E.layout Γ) (state : St E)
 (lookups : LocalArgs locals arguments values)
 (signature : Roadmap.Bytes)
 (memory : LiteralFailureDynamicListError.represented locals state index signature)
 (fields : LiteralFailureMixedEncoding.Represented state values encoded parts) :
 (evalE G F (types.length+extra+5)
  (.abiEncode .encodeWithSignature (.cons (.local index) arguments))).run (locals,state)=
 (.ok (.val (.memRef rfl state.heap.next)),
  (locals,SourceKeccak.afterLiteral state ((wordBytes (G.fixed.hash signature)).take 4++AbiEntry.encodeArgs encoded))) :=
 SourceAbi.signature_execute G F (types.length+extra+4) (.cons (.local index) arguments)
 locals locals locals locals state state state state (.val (locals.get index)) values.toR
 signature (AbiEntry.encodeArgs encoded)
 (arguments_run G F extra index locals state lookups)
 (LiteralFailureSignatureBytes.signature_read F _ index signature locals locals state memory)
 (LiteralFailureMixedEncoding.encoding_run F _ locals state fields)

theorem rethrow_run {E : Env} {Γ types shapes} {arguments : RArgs E Γ types}
 {values : Source.Vals E.layout types} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra statementFuel : Nat) (index : Source.Idx Γ (.bytes .memory))
 (locals : Locals E.layout Γ) (state : St E)
 (lookups : LocalArgs locals arguments values)
 (signature : Roadmap.Bytes)
 (memory : LiteralFailureDynamicListError.represented locals state index signature)
 (fields : LiteralFailureMixedEncoding.Represented state values encoded parts) :
 (SourceRethrow.fromExpression G F (types.length+extra+5) (statementFuel+1)
  (.abiEncode .encodeWithSignature (.cons (.local index) arguments))).run (locals,state)=
 (.error (.revert ((wordBytes (G.fixed.hash signature)).take 4++AbiEntry.encodeArgs encoded)),
  (locals,SourceKeccak.afterLiteral state ((wordBytes (G.fixed.hash signature)).take 4++AbiEntry.encodeArgs encoded))) :=
 SourceRethrow.expression_rethrow G F _ statementFuel _ locals locals state _ state.heap.next _
 (expression_run G F extra index locals state lookups signature memory fields) (SourceKeccak.allocated state _)

theorem statement_timeout {E : Env} {Γ types shapes} {arguments : RArgs E Γ types}
 {values : Source.Vals E.layout types} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra : Nat) (index : Source.Idx Γ (.bytes .memory))
 (locals : Locals E.layout Γ) (state : St E)
 (lookups : LocalArgs locals arguments values)
 (signature : Roadmap.Bytes)
 (memory : LiteralFailureDynamicListError.represented locals state index signature)
 (fields : LiteralFailureMixedEncoding.Represented state values encoded parts) :
 (SourceRethrow.fromExpression G F (types.length+extra+5) 0
  (.abiEncode .encodeWithSignature (.cons (.local index) arguments))).run (locals,state)=
 (.error .timeout,
  (locals,SourceKeccak.afterLiteral state ((wordBytes (G.fixed.hash signature)).take 4++AbiEntry.encodeArgs encoded))) := by
 have expression := expression_run G F extra index locals state lookups signature memory fields
 have statement := SourceCustomErrorFailures.rethrow_zero_horizon G F
  (Source.Idx.here : Source.Idx [.bytes .memory] (.bytes .memory))
  (.cons (.memRef rfl state.heap.next) .nil)
  (SourceKeccak.afterLiteral state ((wordBytes (G.fixed.hash signature)).take 4++AbiEntry.encodeArgs encoded))
 dsimp only [ExceptT.run] at expression statement
 simp only [SourceRethrow.fromExpression,EM.sub,getV,RVal.get,EM.lift,
  bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
  StateT.bind,StateT.pure,Except.pure,expression,statement]
end Solidity.Lowering.V08.LiteralFailureMixedSignature
