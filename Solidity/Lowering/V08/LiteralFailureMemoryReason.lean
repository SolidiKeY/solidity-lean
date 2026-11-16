import Solidity.Lowering.V08.LiteralFailureBytesReadback

/-! Existing Source require reasons reached through typed memory.
No new source evaluator, decoder, profile or runtime memory encoder. -/
namespace Solidity.Lowering.V08.LiteralFailureMemoryReason
open Solidity Source Backend

def context (Γ : RCtx) : RCtx := .bool :: .string .memory :: .string .memory :: Γ

def caller {E : Env} {Γ : RCtx} (b : Bool) (current next : Nat) (older : Locals E.layout Γ) :
    Locals E.layout (context Γ) :=
  .cons (.bool b) (.cons (.memRef rfl current) (.cons (.memRef rfl next) older))

def assignMessage {E : Env} {Γ : RCtx} : RExpr E (context Γ) (.string .memory) :=
  .assign (.local (.there .here)) (.local (.there (.there .here)))

def requireAssigned {E : Env} {Γ : RCtx} : RExpr E (context Γ) (.tuple []) :=
  .builtin .require (.cons (.local .here) (.cons assignMessage .nil)) rfl

theorem assignment {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (b : Bool) (current next : Nat) (older : Locals E.layout Γ) (state : St E) :
    (evalE G F (n+8) assignMessage).run (caller b current next older,state) =
      (.ok (.val (.memRef rfl next)),(caller b next next older,state)) := by rfl

/-- Arguments are evaluated even on success; no heap-read premise is needed. -/
theorem require_true {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (current next : Nat) (older : Locals E.layout Γ) (state : St E) :
    (evalE G F (n+8) requireAssigned).run (caller true current next older,state) =
      (.ok RVal.unit,(caller true next next older,state)) := by rfl

theorem require_false {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (current next : Nat) (older : Locals E.layout Γ) (state : St E) (bs : Roadmap.Bytes)
    (heap : state.heap.get next = some ⟨.string .memory,.string bs⟩) :
    (evalE G F (n+8) requireAssigned).run (caller false current next older,state) =
      (.error (.revert (errorData bs)),(caller false next next older,state)) := by
  dsimp [requireAssigned,assignMessage,caller,evalE,withLibraryCalldata,evalBuiltin,evalArgs,evalLoc,writeLoc,
    getV,RVal.get,bytesOfRV,heapBytes,heapObj,EM.st,EM.locals,EM.lift,EM.setLocals]
  dsimp [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,
    liftM,monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,
    modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,Except.pure,Locals.get,Locals.set]
  first | (rw [heap]; rfl) | rfl
end Solidity.Lowering.V08.LiteralFailureMemoryReason
