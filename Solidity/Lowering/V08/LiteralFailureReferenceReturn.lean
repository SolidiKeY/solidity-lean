import Solidity.Lowering.V08.LiteralFailureDynamicReturn

/-! Actual single bytes-memory return statement, hidden-slot extraction and
published encoded-return transport. No unknown-memory runtime encoder. -/
namespace Solidity.Lowering.V08.LiteralFailureReferenceReturn
open Solidity Source Backend

def context (Γ : RCtx) : RCtx := .bytes .memory :: Γ

def before {E : Env} {Γ : RCtx} (old : Source.Val E.layout (.bytes .memory))
 (parameters : Locals E.layout Γ) : Locals E.layout (context Γ) := .cons old parameters

def finished {E : Env} {Γ : RCtx} (parameters : Locals E.layout Γ)
 (index : Source.Idx Γ (.bytes .memory)) : Locals E.layout (context Γ) :=
 .cons (parameters.get index) parameters

def statement {E : Env} {Γ : RCtx} (index : Source.Idx Γ (.bytes .memory)) :
 RStmt E [.bytes .memory] false .body (context Γ) (context Γ) :=
 .retVal rfl (.local (.there index)) rfl

def extracted {E : Env} {Γ : RCtx} (parameters : Locals E.layout Γ)
 (index : Source.Idx Γ (.bytes .memory)) : RVals E.layout [.bytes .memory] :=
 .cons (.val (parameters.get index)) .nil

/-- One hidden return slot, followed by the actual parameter context.
The parameter count is Γ.length; no arbitrary calling convention is inferred. -/
theorem source_run {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra : Nat)
 (old : Source.Val E.layout (.bytes .memory)) (parameters : Locals E.layout Γ)
 (index : Source.Idx Γ (.bytes .memory)) (state : St E) :
 (execS G F (extra+6) Γ.length none (statement index) (before old parameters)).run (L0 E,state)=
 (.ok (.ret (finished parameters index)),(L0 E,state)) := by
 have slot : (context Γ).length-(Γ.length+1)=0 := by
  simp only [context,List.length_cons]
  omega
 simp only [statement,execS,slot,List.length_cons,List.length_nil,
  before,finished,evalE,convRV,getV,RVal.get,EM.sub,EM.locals,EM.lift,
  bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
  StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,
  liftM,monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,
  Except.pure,Locals.get,Locals.setAt,↓reduceDIte]

theorem extraction {E : Env} {Γ : RCtx} (parameters : Locals E.layout Γ)
 (index : Source.Idx Γ (.bytes .memory)) :
 retVals (finished parameters index) 0 [.bytes .memory]=.ok (extracted parameters index) := by rfl

/-- The actual returned reference is extracted and encoded before G38 transport.
Encoding success is derived from heap facts, not assumed as a premise. -/
theorem chain {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra fuel address : Nat)
 (old : Source.Val E.layout (.bytes .memory)) (parameters : Locals E.layout Γ)
 (index : Source.Idx Γ (.bytes .memory)) (bytes : Roadmap.Bytes) (state savedSource : St E)
 (memory : LiteralFailureDynamicListError.represented parameters state index bytes)
 (saved live : Failure.Slice.Machine)
 (fits : Failure.Fits address (LiteralFailureDynamicReturn.payload [bytes]))
 (stack : live.stack.length+2≤1024) :
 (execS G F (extra+6) Γ.length none (statement index) (before old parameters)).run (L0 E,state)=
  (.ok (.ret (finished parameters index)),(L0 E,state)) ∧
 retVals (finished parameters index) 0 [.bytes .memory]=.ok (extracted parameters index) ∧
 FailurePaths.Premises.EncodingAt F fuel (extracted parameters index) state state
  (LiteralFailureDynamicReturn.payload [bytes]) ∧
 FailurePaths.Emits (Failure.emit address (.returned (LiteralFailureDynamicReturn.payload [bytes])))
  address (.returned (LiteralFailureDynamicReturn.payload [bytes])) ∧
 Failure.Local.execute (Failure.Local.save (MemoryOps.Physical.worldJournal savedSource.ex saved))
  address (.returned (LiteralFailureDynamicReturn.payload [bytes])) (MemoryOps.Physical.worldJournal state.ex live)=
 some (MemoryOps.Physical.worldJournal state.ex {live with memory:=Failure.Slice.putBytes live.memory address (LiteralFailureDynamicReturn.payload [bytes])},
  .success (LiteralFailureDynamicReturn.payload [bytes])) :=
 ⟨source_run G F extra old parameters index state,extraction parameters index,
  LiteralFailureDynamicReturn.return_transport F fuel address [index] [bytes] parameters state savedSource
   ⟨memory,trivial⟩ saved live fits stack⟩
end Solidity.Lowering.V08.LiteralFailureReferenceReturn
