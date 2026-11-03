import Solidity.Lowering.V08.LiteralFailureMixedCustomError

/-! Typed string-memory prefix before an arbitrary represented mixed tail.
The string contributes an existing dynamic byte payload, not a new codec or
source admission rule. Heap objects and all execution equations are intrinsic. -/
namespace Solidity.Lowering.V08.LiteralFailureStringPrefix
open Solidity Source

def values {E : Env} {types : RCtx} (address : Nat)
 (tail : Source.Vals E.layout types) : Source.Vals E.layout (.string .memory::types) :=
 .cons (.memRef rfl address) tail

theorem parts_run {E : Env} {Γ types shapes} {tail : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} {parts} (F : Fr) (fuel : Nat)
 (locals : Locals E.layout Γ) (state : St E) (address : Nat) (bs : Roadmap.Bytes)
 (heap : state.heap.get address=some ⟨.string .memory,.string bs⟩)
 (fields : LiteralFailureMixedEncoding.Represented state tail encoded parts) :
 (encodeParts F fuel false (values address tail).toR : EM E Γ _).run (locals,state)=
 (.ok ((true,bs)::parts),(locals,state)) := by
 have actual := LiteralFailureMixedEncoding.parts_run F fuel locals state fields
 simp only [values,Vals.toR,encodeParts,encodeOne,bytesOfRV,heapBytes,heapObj,EM.st,
  bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
  StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,
  monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,heap]
 dsimp only [ExceptT.run] at actual
 rw [actual]
 rfl

theorem encoding_run {E : Env} {Γ types shapes} {tail : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} {parts} (F : Fr) (fuel : Nat)
 (locals : Locals E.layout Γ) (state : St E) (address : Nat) (bs : Roadmap.Bytes)
 (heap : state.heap.get address=some ⟨.string .memory,.string bs⟩)
 (fields : LiteralFailureMixedEncoding.Represented state tail encoded parts) :
 (encodeVals F fuel false (values address tail).toR : EM E Γ _).run (locals,state)=
 (.ok (AbiEntry.encodeArgs (.cons (.bytes bs) encoded)),(locals,state)) := by
 have actual := LiteralFailureMixedEncoding.encoding_run F fuel locals state
  (.bytes address bs (.inr heap) fields)
 exact actual

/-- Discharges the existing G38 encoding premise for a typed string prefix. -/
theorem encodingAt {E : Env} {types shapes} {tail : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} {parts} (F : Fr) (fuel : Nat)
 (state : St E) (address : Nat) (bs : Roadmap.Bytes)
 (heap : state.heap.get address=some ⟨.string .memory,.string bs⟩)
 (fields : LiteralFailureMixedEncoding.Represented state tail encoded parts) :
 Backend.FailurePaths.Premises.EncodingAt F fuel (values address tail).toR state state
  (AbiEntry.encodeArgs (.cons (.bytes bs) encoded)) :=
 encoding_run F fuel (L0 E) state address bs heap fields

/-- The declared error uses the actual string parameter, not a bytes-typed
substitute. Local argument execution and encoding are both derived. -/
theorem source_run {E : Env} {Γ types shapes} {tail : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} {parts}
 {arguments : RConvArgs E Γ (.string .memory::types)}
 (G : Glob E) (F : Fr) (extra : Nat) (error : Decl)
 (typed : error.paramTys E=some (.string .memory::types))
 (locals : Locals E.layout Γ) (state : St E) (address : Nat) (bs : Roadmap.Bytes)
 (lookups : LiteralFailureMixedCustomError.LocalArgs locals arguments (values address tail))
 (heap : state.heap.get address=some ⟨.string .memory,.string bs⟩)
 (fields : LiteralFailureMixedEncoding.Represented state tail encoded parts) :
 (execS G F ((.string .memory::types).length+extra+4) 0 none
  (.revertError error typed arguments : RStmt E [] false .body Γ Γ) locals).run (L0 E,state)=
 (.error (.revert (G.selector (sigOf E.layout error.name (.string .memory::types))++
  AbiEntry.encodeArgs (.cons (.bytes bs) encoded))),(L0 E,state)) :=
 SourceCustomErrors.execute G F ((.string .memory::types).length+extra+3) error typed arguments
 locals locals state state state (values address tail) _
 (LiteralFailureMixedCustomError.arguments_run G F extra locals state lookups)
 (encoding_run F _ (L0 E) state address bs heap fields)

end Solidity.Lowering.V08.LiteralFailureStringPrefix
