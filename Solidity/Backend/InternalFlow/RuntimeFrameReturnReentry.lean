import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV1

/-! Re-entry after an actual return. Reached representation, cursor and
allocator growth establish a second frozen Entry, with explicit layout and
demand comparisons. There is no assumed next simulation or profile. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ReturnReentry
open Evm Evm.Memory

theorem reached_entry {C : Contract} {Γ Δ Ξ : Ctx} {L b frame : Nat} {F : Frag Γ}
 {first : InterfaceV1.Emission C Γ Δ} {next : InterfaceV1.Emission C Δ Ξ}
 {caller : State C Γ} {base : Nat → Fin W} {before : Machine} {start : Nat}
 (entry : InterfaceV1.Entry first L b frame F caller base before start)
 {out : Solidity.Out C caller.H Δ} {addresses : Nat → Fin W} {after : Machine}
 (represented : StateRepr L b frame first.frag out.st addresses after)
 (growth : GrowsAllocator b frame (first.heapCost caller) caller base before out.st addresses after)
 (cursor : after.mem first.pointerCell=.val (wmod start))
 (limit : next.localLimit=first.localLimit) (pointer : next.pointerCell=first.pointerCell)
 (need : next.need≤first.need) (resultBound : b+Ξ.length≤first.localLimit)
 (arena : next.arenaWords out.st≤first.arenaWords caller)
 (controls : Δ.length+1≤next.arenaWords out.st)
 (capacity : AllocationInput b frame (first.heapCost caller+next.heapCost out.st) caller base before) :
 InterfaceV1.Entry next L b frame first.frag out.st addresses after start := by
 refine ⟨represented,?_,?_,?_,?_,?_,?_,?_,controls,?_,?_,?_,growth.nextInput capacity⟩
 · simpa only [limit] using entry.resultBound
 · simpa only [limit] using resultBound
 · rw [limit]
   have bound := entry.workspace
   omega
 · simpa only [limit,pointer] using entry.pointerAbove
 · simpa only [pointer] using entry.pointerBelow
 · simpa only [limit] using entry.payloadAbove
 · have bound := entry.reserve
   omega
 · rcases entry.separate with below | above
   · exact .inl (by simpa only [pointer] using below)
   · exact .inr (by rw [pointer];omega)
 · have bound := entry.noWrap
   omega
 · simpa only [pointer] using cursor

/-- An actual successful return supplies all dynamic fields of the next
entry. Layout and demand comparisons remain explicit resource conditions. -/
theorem after_return {C : Contract} {Γ Δ Ξ : Ctx} {L b frame : Nat} {F : Frag Γ}
 {first : InterfaceV1.Emission C Γ Δ} {next : InterfaceV1.Emission C Δ Ξ}
 {caller : State C Γ} {base : Nat → Fin W} {before : Machine} {start : Nat}
 (entry : InterfaceV1.Entry first L b frame F caller base before start)
 {out : Solidity.Out C caller.H Δ}
 (returned : InterfaceV1.Returned first L b frame caller base before start out)
 (limit : next.localLimit=first.localLimit) (pointer : next.pointerCell=first.pointerCell)
 (need : next.need≤first.need) (resultBound : b+Ξ.length≤first.localLimit)
 (arena : next.arenaWords out.st≤first.arenaWords caller)
 (controls : Δ.length+1≤next.arenaWords out.st)
 (capacity : AllocationInput b frame (first.heapCost caller+next.heapCost out.st) caller base before) :
 ∃ after addresses,
 run first.code before=.ok after 0 ∧
 InterfaceV1.Entry next L b frame first.frag out.st addresses after start ∧
 after.stack=before.stack ∧ BaseExtends caller.H base addresses ∧
 GrowsAllocator b frame (first.heapCost caller) caller base before out.st addresses after ∧
 Footprint.Words first.localLimit start before after := by
 obtain ⟨after,addresses,executed,represented,stack,extended,growth,cursor,words⟩ := returned
 exact ⟨after,addresses,executed,reached_entry entry represented growth cursor limit pointer need resultBound arena controls capacity,
   stack,extended,growth,words⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.ReturnReentry
