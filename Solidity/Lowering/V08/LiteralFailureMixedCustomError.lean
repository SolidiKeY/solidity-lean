import Solidity.Lowering.V08.LiteralFailureMixedEncoding

/-! Actual declared custom-error execution for arbitrary mixed word/bytes
arguments. Converted locals are existing indexed RConvArgs; no new AST,
admission predicate, encoder run or source/target simulation is assumed. -/
namespace Solidity.Lowering.V08.LiteralFailureMixedCustomError
open Solidity Source

inductive LocalArgs {E : Env} {Γ : RCtx} (locals : Locals E.layout Γ) :
 {types : RCtx} → RConvArgs E Γ types → Source.Vals E.layout types → Prop
 | nil : LocalArgs locals .nil .nil
 | cons {τ types arguments values} (index : Source.Idx Γ τ)
   (typed : τ.implicit E.isBase E.mapFree τ=true)
   (tail : @LocalArgs E Γ locals types arguments values) :
   LocalArgs locals (.cons (.local index) typed arguments) (.cons (locals.get index) values)

theorem arguments_run {E : Env} {Γ types} {arguments : RConvArgs E Γ types}
 {values : Source.Vals E.layout types} (G : Glob E) (F : Fr) (extra : Nat)
 (locals : Locals E.layout Γ) (state : St E) (lookups : LocalArgs locals arguments values) :
 (evalConvArgs G F (types.length+extra+3) arguments).run (locals,state)=
 (.ok values,(locals,state)) := by
 induction lookups with
 | nil => rfl
 | @cons τ types arguments values index typed tail ih =>
  simp only [List.length_cons]
  rw [evalConvArgs]
  simp only [evalE,convRV,↓reduceDIte,getV,RVal.get,EM.locals,EM.lift,
   bind,pure,Except.pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
   StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,
   monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map]
  have fuel : types.length+1+extra+2=types.length+extra+3 := by omega
  simp only [fuel]
  dsimp only [ExceptT.run] at ih
  rw [ih]
  rfl

theorem source_run {E : Env} {Γ types shapes} {arguments : RConvArgs E Γ types}
 {values : Source.Vals E.layout types} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra : Nat) (error : Decl) (typed : error.paramTys E=some types)
 (locals : Locals E.layout Γ) (state : St E)
 (lookups : LocalArgs locals arguments values)
 (fields : LiteralFailureMixedEncoding.Represented state values encoded parts) :
 (execS G F (types.length+extra+4) 0 none
  (.revertError error typed arguments : RStmt E [] false .body Γ Γ) locals).run (L0 E,state)=
 (.error (.revert (G.selector (sigOf E.layout error.name types)++AbiEntry.encodeArgs encoded)),(L0 E,state)) :=
 SourceCustomErrors.execute G F (types.length+extra+3) error typed arguments
 locals locals state state state values (AbiEntry.encodeArgs encoded)
 (arguments_run G F extra locals state lookups)
 (LiteralFailureMixedEncoding.encoding_run F _ (L0 E) state fields)
end Solidity.Lowering.V08.LiteralFailureMixedCustomError
