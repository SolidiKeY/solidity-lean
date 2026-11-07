import Solidity.Lowering.V08.SourceCustomErrors

/-! Failure boundaries of the published custom-error statement. The argument
locals are private to EM.sub; its reached St survives a halt. Encoding executes
in the outer empty local frame. Neither law is an ABI/body adequacy theorem. -/
namespace Solidity.Lowering.V08.SourceCustomErrorFailures
open Solidity Source

theorem arguments_failure {E : Source.Env} {Γ : RCtx} {types : List STy}
    (global : Glob E) (frame : Fr) (horizon : Nat) (error : Decl)
    (typed : error.paramTys E = some types) (args : RConvArgs E Γ types)
    (locals reached : Source.Locals E.layout Γ) (state final : Source.St E) (halt : Source.Halt)
    (arguments : (Source.evalConvArgs global frame horizon args).run (locals,state) =
      (.error halt,(reached,final))) :
    (Source.execS global frame (horizon+1) 0 none
      (.revertError error typed args : RStmt E [] false .body Γ Γ) locals).run (Source.L0 E,state) =
      (.error halt,(Source.L0 E,final)) := by
  simp only [ExceptT.run] at arguments
  simp only [Source.execS,Source.EM.sub,bind,pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,arguments]

theorem encoding_failure {E : Source.Env} {Γ : RCtx} {types : List STy}
    (global : Glob E) (frame : Fr) (horizon : Nat) (error : Decl)
    (typed : error.paramTys E = some types) (args : RConvArgs E Γ types)
    (locals next : Source.Locals E.layout Γ) (state middle final : Source.St E)
    (values : Source.Vals E.layout types) (halt : Source.Halt)
    (arguments : (Source.evalConvArgs global frame horizon args).run (locals,state) =
      (.ok values,(next,middle)))
    (encoding : (Source.encodeVals frame horizon false values.toR : Source.EM E [] _).run
      (Source.L0 E,middle) = (.error halt,(Source.L0 E,final))) :
    (Source.execS global frame (horizon+1) 0 none
      (.revertError error typed args : RStmt E [] false .body Γ Γ) locals).run (Source.L0 E,state) =
      (.error halt,(Source.L0 E,final)) := by
  simp only [ExceptT.run] at arguments encoding
  simp only [Source.execS,Source.EM.sub,bind,pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,arguments,encoding]

/-- A successful first converted argument followed by a failing tail; no later
argument, encoding or custom selector is reached. -/
theorem converted_tail_failure {E : Source.Env} {Γ : RCtx} {σ τ : STy} {types : List STy}
    (global : Glob E) (frame : Fr) (horizon : Nat) (expr : RExpr E Γ σ)
    (conversion : σ.implicit E.isBase E.mapFree τ = true) (tail : RConvArgs E Γ types)
    (locals middle reached : Source.Locals E.layout Γ) (state interim final : Source.St E)
    (value : Source.Val E.layout τ) (halt : Source.Halt)
    (head : (do Source.getV (← Source.convRV frame horizon τ (← Source.evalE global frame horizon expr)) :
      Source.EM E Γ _).run (locals,state) = (.ok value,(middle,interim)))
    (rest : (Source.evalConvArgs global frame horizon tail).run (middle,interim) =
      (.error halt,(reached,final))) :
    (Source.evalConvArgs global frame (horizon+1) (.cons expr conversion tail)).run (locals,state) =
      (.error halt,(reached,final)) := by
  let converted : Source.EM E Γ (Source.Val E.layout τ) :=
    do Source.getV (← Source.convRV frame horizon τ (← Source.evalE global frame horizon expr))
  have group : Source.evalConvArgs global frame (horizon+1) (.cons expr conversion tail) =
      (do let v ← converted
          pure (.cons v (← Source.evalConvArgs global frame horizon tail))) := by
    simp only [Source.evalConvArgs,converted,bind_assoc]
  rw [group]
  change converted.run (locals,state) = _ at head
  simp only [ExceptT.run] at head rest
  simp only [bind,pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,head,rest]

/-- The existing observation combinator retains the failure and reached complete
state; this is EM.attempt, not Solidity try/catch admission. -/
theorem attempt_failure {E : Source.Env} {Γ : RCtx} {α : Type}
    (computation : Source.EM E Γ α) (locals reached : Source.Locals E.layout Γ)
    (state final : Source.St E) (halt : Source.Halt)
    (execution : computation.run (locals,state) = (.error halt,(reached,final))) :
    (Source.EM.attempt computation).run (locals,state) =
      (.ok (.error halt),(reached,final)) := by
  simp only [ExceptT.run] at execution
  simp only [Source.EM.attempt,ExceptT.run,ExceptT.mk,execution]

/-- The published canonical rethrow reads the exact bytes of an actually present
memory object. No catch-clause selection or ABI decoding is assumed. -/
theorem rethrow_bytes {E : Source.Env} {Γ : RCtx}
    (global : Glob E) (frame : Fr) (horizon : Nat) (index : Source.Idx Γ (.bytes .memory))
    (locals : Source.Locals E.layout Γ) (state : Source.St E) (address : Nat) (data : Roadmap.Bytes)
    (reference : locals.get index = .memRef rfl address)
    (memory : state.heap.get address = some ⟨.bytes .memory,.bytes data⟩) :
    (Source.execS global frame (horizon+1) 0 none
      (.rethrow index : RStmt E [] false .body Γ Γ) locals).run (Source.L0 E,state) =
      (.error (.revert data),(Source.L0 E,state)) := by
  simp only [Source.execS,reference,Source.heapBytes,Source.heapObj,Source.EM.st,
    bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,monadLift,
    MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,memory,Source.EM.halt,throw,throwThe,MonadExceptOf.throw]

theorem rethrow_zero_horizon {E : Source.Env} {Γ : RCtx}
    (global : Glob E) (frame : Fr) (index : Source.Idx Γ (.bytes .memory))
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS global frame 0 0 none
      (.rethrow index : RStmt E [] false .body Γ Γ) locals).run (Source.L0 E,state) =
      (.error .timeout,(Source.L0 E,state)) := rfl

#print axioms rethrow_bytes
#print axioms rethrow_zero_horizon

#print axioms arguments_failure
#print axioms encoding_failure
#print axioms converted_tail_failure
#print axioms attempt_failure
end Solidity.Lowering.V08.SourceCustomErrorFailures
