import Solidity.Lowering.V08.LiteralFailureMixedEncoding
import Solidity.Lowering.V08.SourceRethrow

/-! Local argument lookup and actual heterogeneous ABI expression allocation.
The relations below refer to existing intrinsic arguments and values; they do
not assume a run, add an AST, or define a source admission predicate. -/
namespace Solidity.Lowering.V08.LiteralFailureMixedExpression
open Solidity Source

inductive LocalArgs {E : Env} {Γ : RCtx} (locals : Locals E.layout Γ) :
 {types : RCtx} → RArgs E Γ types → Source.Vals E.layout types → Prop
 | nil : LocalArgs locals .nil .nil
 | cons {τ types arguments values} (index : Source.Idx Γ τ)
   (tail : @LocalArgs E Γ locals types arguments values) :
   LocalArgs locals (.cons (.local index) arguments) (.cons (locals.get index) values)

theorem arguments_run {E : Env} {Γ types} {arguments : RArgs E Γ types}
 {values : Source.Vals E.layout types} (G : Glob E) (F : Fr) (extra : Nat)
 (locals : Locals E.layout Γ) (state : St E) (lookups : LocalArgs locals arguments values) :
 (evalArgs G F (types.length+extra+3) arguments).run (locals,state)=
 (.ok values.toR,(locals,state)) := by
 induction lookups with
 | nil => rfl
 | @cons τ types arguments values index tail ih =>
  simp only [List.length_cons,Vals.toR]
  rw [evalArgs]
  simp only [evalE,EM.locals,bind,pure,
   ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
   StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,
   monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map]
  have fuel : types.length+1+extra+2=types.length+extra+3 := by omega
  simp only [fuel]
  dsimp only [ExceptT.run] at ih
  rw [ih]
  rfl
theorem expression_run {E : Env} {Γ types shapes} {arguments : RArgs E Γ types}
 {values : Source.Vals E.layout types} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra : Nat) (locals : Locals E.layout Γ) (state : St E)
 (lookups : LocalArgs locals arguments values)
 (fields : LiteralFailureMixedEncoding.Represented state values encoded parts) :
 (evalE G F (types.length+extra+4) (.abiEncode .encode arguments)).run (locals,state)=
 (.ok (.val (.memRef rfl state.heap.next)),
  (locals,SourceKeccak.afterLiteral state (AbiEntry.encodeArgs encoded))) :=
 SourceAbi.execute G F (types.length+extra+3) false arguments locals locals locals
 state state state values.toR (AbiEntry.encodeArgs encoded)
 (arguments_run G F extra locals state lookups)
 (LiteralFailureMixedEncoding.encoding_run F _ locals state fields)

/-- Actual allocation preserves every previously occupied address. Freshness
is derived from the existing intrinsic heap bound, not a disjointness premise. -/
theorem old_object {E : Env} (state : St E) (packet : Roadmap.Bytes) (address : Nat)
 (object : Σ τ, Source.Data E.layout τ) (present : state.heap.get address=some object) :
 (SourceKeccak.afterLiteral state packet).heap.get address=some object := by
 have different : address≠state.heap.next := by
  intro equal
  have empty := state.heap.bounded address (by omega)
  change state.heap.get address=none at empty
  rw [present] at empty
  cases empty
 exact (Source.Heap.alloc_other state.heap ⟨.bytes .memory,.bytes packet⟩ different).trans present

/-- Every concrete mixed input-field fact survives the fresh result object. -/
theorem fields_after {E : Env} {types shapes} {values : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} {parts} (state : St E) (packet : Roadmap.Bytes)
 (fields : LiteralFailureMixedEncoding.Represented state values encoded parts) :
 LiteralFailureMixedEncoding.Represented (SourceKeccak.afterLiteral state packet) values encoded parts := by
 induction fields with
 | nil => exact .nil
 | uint w tail ih => exact .uint w ih
 | bytes address bs heap tail ih =>
  apply LiteralFailureMixedEncoding.Represented.bytes address bs _ ih
  rcases heap with heap | heap
  · exact .inl (old_object state packet address _ heap)
  · exact .inr (old_object state packet address _ heap)

theorem rethrow_run {E : Env} {Γ types shapes} {arguments : RArgs E Γ types}
 {values : Source.Vals E.layout types} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra statementFuel : Nat) (locals : Locals E.layout Γ) (state : St E)
 (lookups : LocalArgs locals arguments values)
 (fields : LiteralFailureMixedEncoding.Represented state values encoded parts) :
 (SourceRethrow.fromExpression G F (types.length+extra+4) (statementFuel+1)
  (.abiEncode .encode arguments)).run (locals,state)=
 (.error (.revert (AbiEntry.encodeArgs encoded)),
  (locals,SourceKeccak.afterLiteral state (AbiEntry.encodeArgs encoded))) :=
 SourceRethrow.expression_rethrow G F _ statementFuel (.abiEncode .encode arguments)
 locals locals state _ state.heap.next _ (expression_run G F extra locals state lookups fields)
 (SourceKeccak.allocated state _)
theorem statement_timeout {E : Env} {Γ types shapes} {arguments : RArgs E Γ types}
 {values : Source.Vals E.layout types} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra : Nat) (locals : Locals E.layout Γ) (state : St E)
 (lookups : LocalArgs locals arguments values)
 (fields : LiteralFailureMixedEncoding.Represented state values encoded parts) :
 (SourceRethrow.fromExpression G F (types.length+extra+4) 0
  (.abiEncode .encode arguments)).run (locals,state)=
 (.error .timeout,(locals,SourceKeccak.afterLiteral state (AbiEntry.encodeArgs encoded))) := by
 have expression := expression_run G F extra locals state lookups fields
 have statement := SourceCustomErrorFailures.rethrow_zero_horizon G F
  (Source.Idx.here : Source.Idx [.bytes .memory] (.bytes .memory))
  (.cons (.memRef rfl state.heap.next) .nil)
  (SourceKeccak.afterLiteral state (AbiEntry.encodeArgs encoded))
 dsimp only [ExceptT.run] at expression statement
 simp only [SourceRethrow.fromExpression,EM.sub,getV,RVal.get,EM.lift,
  bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
  StateT.bind,StateT.pure,Except.pure,expression,statement]

theorem expression_timeout {E : Env} {Γ types} (G : Glob E) (F : Fr)
 (arguments : RArgs E Γ types) (statementFuel : Nat)
 (locals : Locals E.layout Γ) (state : St E) :
 (SourceRethrow.fromExpression G F 0 statementFuel (.abiEncode .encode arguments)).run (locals,state)=
 (.error .timeout,(locals,state)) :=
 SourceRethrow.expression_failure G F 0 statementFuel (.abiEncode .encode arguments)
 locals locals state state .timeout rfl
end Solidity.Lowering.V08.LiteralFailureMixedExpression
