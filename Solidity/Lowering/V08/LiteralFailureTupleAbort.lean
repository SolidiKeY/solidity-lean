import Solidity.Lowering.V08.LiteralFailureReturnSlots

/-! Failure of the actual tuple-return argument evaluation. Local effects in
that subcomputation are discarded by EM.sub; its actual Source state survives.
The statement's later setRets phase is not reached; argument expressions
may themselves change slots. No result encoding is inferred. -/
namespace Solidity.Lowering.V08.LiteralFailureTupleAbort
open Solidity Source

/-- This conditional boundary is discharged by actual executions in Controls.
It preserves the exact Halt, including payload, timeout and stuck cases. -/
theorem argument_error {E : Env} {types Γ : RCtx}
 (G : Glob E) (F : Fr) (n nps : Nat) (arguments : RConvArgs E Γ types)
 (initial changed : Locals E.layout Γ) (state final : St E) (halt : Halt)
 (run : (evalConvArgs G F n arguments).run (initial,state)=
  (.error halt,(changed,final))) :
 (execS G F (n+1) nps none
  (.retTuple arguments : RStmt E types false .body Γ Γ) initial).run (L0 E,state)=
 (.error halt,(L0 E,final)) := by
 dsimp only [ExceptT.run] at run
 first
 | (simp only [execS,EM.sub,bind,ExceptT.bind,ExceptT.bindCont,ExceptT.run,
    ExceptT.mk,StateT.bind,run]; rfl)
 | rfl
end Solidity.Lowering.V08.LiteralFailureTupleAbort
