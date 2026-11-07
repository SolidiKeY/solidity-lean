import Solidity.Lowering.V08.LiteralFailureMixedExpression
import Solidity.Lowering.V08.LiteralFailureSelectorBytes

/-! Actual encodeWithSelector for heterogeneous local arguments. This consumes
published lookup, conversion, codec and allocation semantics, not dispatch or
an assumed same-invocation/target correspondence. -/
namespace Solidity.Lowering.V08.LiteralFailureMixedSelector
open Solidity Source
open LiteralFailureMixedExpression (LocalArgs)
abbrev Selector := LiteralFailureSelectorBytes.Selector

theorem arguments_run {E : Env} {Γ types} {arguments : RArgs E Γ types}
 {values : Source.Vals E.layout types} (G : Glob E) (F : Fr) (extra : Nat)
 (index : Source.Idx Γ Selector) (locals : Locals E.layout Γ) (state : St E)
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
 (G : Glob E) (F : Fr) (extra : Nat) (index : Source.Idx Γ Selector)
 (locals : Locals E.layout Γ) (state : St E)
 (lookups : LocalArgs locals arguments values)
 (fields : LiteralFailureMixedEncoding.Represented state values encoded parts) :
 (evalE G F (types.length+extra+5)
  (.abiEncode .encodeWithSelector (.cons (.local index) arguments))).run (locals,state)=
 (.ok (.val (.memRef rfl state.heap.next)),
  (locals,SourceKeccak.afterLiteral state ((locals.get index).bytesOf++AbiEntry.encodeArgs encoded))) :=
 SourceAbi.selector_execute G F (types.length+extra+4) (.cons (.local index) arguments)
 locals locals locals locals state state state state (.val (locals.get index)) values.toR
 (locals.get index) (AbiEntry.encodeArgs encoded)
 (arguments_run G F extra index locals state lookups)
 (LiteralFailureSelectorBytes.conversion_run F _ _ locals state)
 (LiteralFailureMixedEncoding.encoding_run F _ locals state fields)

theorem rethrow_run {E : Env} {Γ types shapes} {arguments : RArgs E Γ types}
 {values : Source.Vals E.layout types} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra statementFuel : Nat) (index : Source.Idx Γ Selector)
 (locals : Locals E.layout Γ) (state : St E)
 (lookups : LocalArgs locals arguments values)
 (fields : LiteralFailureMixedEncoding.Represented state values encoded parts) :
 (SourceRethrow.fromExpression G F (types.length+extra+5) (statementFuel+1)
  (.abiEncode .encodeWithSelector (.cons (.local index) arguments))).run (locals,state)=
 (.error (.revert ((locals.get index).bytesOf++AbiEntry.encodeArgs encoded)),
  (locals,SourceKeccak.afterLiteral state ((locals.get index).bytesOf++AbiEntry.encodeArgs encoded))) :=
 SourceRethrow.expression_rethrow G F _ statementFuel _ locals locals state _ state.heap.next _
 (expression_run G F extra index locals state lookups fields) (SourceKeccak.allocated state _)

theorem statement_timeout {E : Env} {Γ types shapes} {arguments : RArgs E Γ types}
 {values : Source.Vals E.layout types} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra : Nat) (index : Source.Idx Γ Selector)
 (locals : Locals E.layout Γ) (state : St E)
 (lookups : LocalArgs locals arguments values)
 (fields : LiteralFailureMixedEncoding.Represented state values encoded parts) :
 (SourceRethrow.fromExpression G F (types.length+extra+5) 0
  (.abiEncode .encodeWithSelector (.cons (.local index) arguments))).run (locals,state)=
 (.error .timeout,
  (locals,SourceKeccak.afterLiteral state ((locals.get index).bytesOf++AbiEntry.encodeArgs encoded))) := by
 have expression := expression_run G F extra index locals state lookups fields
 have statement := SourceCustomErrorFailures.rethrow_zero_horizon G F
  (Source.Idx.here : Source.Idx [.bytes .memory] (.bytes .memory))
  (.cons (.memRef rfl state.heap.next) .nil)
  (SourceKeccak.afterLiteral state ((locals.get index).bytesOf++AbiEntry.encodeArgs encoded))
 dsimp only [ExceptT.run] at expression statement
 simp only [SourceRethrow.fromExpression,EM.sub,getV,RVal.get,EM.lift,
  bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
  StateT.bind,StateT.pure,Except.pure,expression,statement]
end Solidity.Lowering.V08.LiteralFailureMixedSelector
