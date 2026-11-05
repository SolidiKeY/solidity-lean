import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV1
import Solidity.Evm.MemoryCalls

/-! A checked continuation after an actual represented return. The capacity
split uses the same prefix growth and reached source state. No midpoint,
target simulation, global heap preservation or failed state is assumed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ReturnContinuation
open Evm Evm.Memory

/-- Continue from the actual return of a statement. The return producer stays
an explicit premise of this general law; concrete clients must discharge it. -/
theorem after_return {C : Contract} {Γ Δ Ξ : Ctx} {L b frame : Nat} {F : Frag Γ}
 {statement : Stmt C Γ Δ} {plan : InterfaceV1.Emission C Γ Δ}
 (returns : InterfaceV1.ReturnClaim b F statement plan)
 {caller : State C Γ} {base : Nat → Fin W} {before : Machine} {start : Nat}
 (entry : InterfaceV1.Entry plan L b frame F caller base before start)
 {out : Solidity.Out C caller.H Δ} (source : statement.run caller=.ok out)
 (suffix : Prog C Δ Ξ) (checked : Calls.Program b plan.frag suffix)
 (room : b+checked.need≤frame)
 (capacity : AllocationInput b frame (plan.heapCost caller+checked.cost out.st) caller base before) :
 GrowingResult L b frame (plan.heapCost caller+checked.cost out.st) checked.frag caller base before
   ((.cons statement suffix : Prog C Γ Ξ).run caller)
   (run (plan.code++checked.code) before) := by
 obtain ⟨middle,addresses,executed,represented,stack,extended,growth,cursor,words⟩ :=
   returns L frame caller base before start entry out source
 have reached := growth.nextInput capacity
 have result := checked.sound represented room reached
 rcases result with ⟨last,final,finalBase,suffixSource,suffixTarget,suffixRepr,suffixStack,suffixBase,suffixGrowth⟩ |
   ⟨suffixSource,suffixTarget⟩
 · refine .inl ⟨⟨last.st,out.ext.trans last.ext⟩,final,finalBase,?_,?_,suffixRepr,
     suffixStack.trans stack,BaseExtends.trans out.ext extended suffixBase,growth.comp suffixGrowth⟩
   · rw [Prog.run_cons_ok source,suffixSource]
     rfl
   · exact (run_append_ok executed).trans suffixTarget
 · refine .inr ⟨?_,(run_append_ok executed).trans suffixTarget⟩
   rw [Prog.run_cons_ok source,suffixSource]
   rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.ReturnContinuation
