import Solidity.Evm.MemoryLoopHorizonObjectNewInventory
import Solidity.Evm.MemoryLoopHorizonObjectOldHeaders
import Solidity.Evm.MemoryLoopHorizonAppend

/-! Retention of arrays created before a finite allocating-loop pause.
The first actual run constructs typed empty arrays. Its complete allocator
growth derives the remaining demand from the original summed budget; resumed
execution preserves their header cells at the same physical addresses. The
iterator append law identifies that actual continuation with the full horizon.
No extra allocator capacity, termination or source adequacy is assumed. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem target_retained_new_headers {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (elapsed remaining : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame (elapsed + remaining) state base machine) :
    ∃ (out : Solidity.Out C state.H Γ) (midBase : Nat → Fin W) (mid reached : Machine),
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        elapsed machine = .inl mid ∧
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        remaining mid = .inl reached ∧
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        (elapsed + remaining) machine = .inl reached ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) body state out elapsed elapsed ∧
      (∀ i, i < elapsed → ∃ r : HRef out.st.H (.array (.prim .uint)),
        r.id = state.H.length + i ∧
        mid.mem (midBase r.id).val = w[0] ∧
        reached.mem (midBase r.id).val = mid.mem (midBase r.id).val) := by
  obtain ⟨out,midBase,mid,firstRun,source,hp,current,stack,bases,grows⟩ :=
    target_pending compiled elapsed repr capacity (demand.of_le (by omega))
  have tailInput : Objects.AllocationInput b frame remaining out.st midBase mid :=
    grows.nextInput demand
  obtain ⟨reached,tailRun,preserved⟩ :=
    target_old_array_headers compiled remaining current capacity tailInput
  have fullRun := (loopIterN_add_of_pending firstRun remaining).trans tailRun
  refine ⟨out,midBase,mid,reached,firstRun,tailRun,fullRun,hp,?_⟩
  intro i within
  obtain ⟨r,identity,empty⟩ := prefix_new_ref hp i within
  have header := (current.heap.arrays .dyn r).length rfl
  exact ⟨r,identity,by simpa only [empty] using header,preserved (.prim .uint) r⟩

end Solidity.Evm.Memory.HorizonObjectAllocating
