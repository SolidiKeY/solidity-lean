import Solidity.Lowering.V08.LiteralFailureStringConversion
import Solidity.Lowering.V08.LiteralFailureStatementReason

/-! Actual eager calldata-string conversion before require. Both the success
and error branches retain the actual copied object. No source admission,
transaction rollback or target memory encoder is introduced. -/
namespace Solidity.Lowering.V08.LiteralFailureCopiedReason
open Solidity Source

def context (Γ : RCtx) : RCtx := .bool :: .string .calldata :: Γ
def caller {E : Env} {Γ : RCtx} (condition : Bool) (off len : Nat) (older : Locals E.layout Γ) :
 Locals E.layout (context Γ) := .cons (.bool condition) (.cons (.cdRef rfl off len) older)
def reason {E : Env} {Γ : RCtx} : RExpr E (context Γ) (.string .memory) :=
 .conv (.local (.there .here)) (.inl rfl)
def arguments {E : Env} {Γ : RCtx} : RArgs E (context Γ) [.bool,.string .memory] :=
 .cons (.local .here) (.cons reason .nil)
def expression {E : Env} {Γ : RCtx} : RExpr E (context Γ) (.tuple []) := .builtin .require arguments rfl

theorem success {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra off len : Nat)
 (older : Locals E.layout Γ) (state : St E) :
 (evalE G F (extra+8) expression).run (caller true off len older,state)=
 (.ok RVal.unit,(caller true off len older,LiteralFailureStringConversion.afterString state ((F.cd.drop off).take len))) := by
 rfl

theorem failure {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra off len : Nat)
 (older : Locals E.layout Γ) (state : St E) :
 (evalE G F (extra+8) expression).run (caller false off len older,state)=
 (.error (.revert (errorData ((F.cd.drop off).take len))),
 (caller false off len older,LiteralFailureStringConversion.afterString state ((F.cd.drop off).take len))) := by
 have order : ((decide (Builtin.require=Builtin.addmod) || decide (Builtin.require=Builtin.mulmod)) && decide (G.pipeline=Roadmap.Pipeline.legacy))=false := by rfl
 have copied := LiteralFailureStringConversion.copy_run F (extra+3) off len (caller false off len older) state
 have object := LiteralFailureStringConversion.allocated state ((F.cd.drop off).take len)
 dsimp only [ExceptT.run,caller] at copied
 simp only [expression,arguments,reason,evalE,evalBuiltin,evalArgs,caller,Locals.get,
  order,Bool.false_eq_true,↓reduceIte,
  EM.locals,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
  StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,monadLift,
  MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,copied,
  getV,RVal.get,EM.lift,Except.pure,bytesOfRV,heapBytes,heapObj,EM.st,object]
 rfl

theorem statement_success {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra off len : Nat)
 (older : Locals E.layout Γ) (state : St E) :
 (execS G F (extra+9) 0 none (.expr expression : RStmt E [] false .body (context Γ) (context Γ))
 (caller true off len older)).run (L0 E,state)=
 (.ok (.normal (caller true off len older)),
 (L0 E,LiteralFailureStringConversion.afterString state ((F.cd.drop off).take len))) := rfl

theorem statement_failure {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra off len : Nat)
 (older : Locals E.layout Γ) (state : St E) :
 (execS G F (extra+9) 0 none (.expr expression : RStmt E [] false .body (context Γ) (context Γ))
 (caller false off len older)).run (L0 E,state)=
 (.error (.revert (errorData ((F.cd.drop off).take len))),
 (L0 E,LiteralFailureStringConversion.afterString state ((F.cd.drop off).take len))) :=
 LiteralFailureStatementReason.expression_error G F (extra+8) expression _ _ _ _ _
  (failure G F extra off len older state)

/-- Logical readback of the bytes from the actual completed error. The length
bound is codec representability, not a new source admission condition. -/
theorem failure_readback {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra off len : Nat)
 (older : Locals E.layout Γ) (state : St E) (bound : ((F.cd.drop off).take len).length<256^32) :
 (evalE G F (extra+8) expression).run (caller false off len older,state)=
 (.error (.revert (errorData ((F.cd.drop off).take len))),
 (caller false off len older,LiteralFailureStringConversion.afterString state ((F.cd.drop off).take len))) ∧
 Semantics.decodeError (errorData ((F.cd.drop off).take len))=some ((F.cd.drop off).take len) := by
 refine ⟨failure G F extra off len older state,?_⟩
 rw [errorData_transport_total]
 exact Backend.AbiWorld.error_roundtrip _ bound

end Solidity.Lowering.V08.LiteralFailureCopiedReason
