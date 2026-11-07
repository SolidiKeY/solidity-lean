import Solidity.Evm.MemoryLoopHorizonObjectAllocatingTarget
import Solidity.Evm.MemoryLoopHorizonObjectHeapKeeps

/-! Physical preservation of every original dynamic-array header by the
actual allocating loop target. Source old-object preservation and base
extension transport the initial array representation; the reached complete
representation fixes the same header value. This is limited to original live
dynamic-array header cells, not arbitrary memory or general stores/copies. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem target_old_array_headers {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame n state base machine) :
    ∃ reached,
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      (∀ (E : Ty) (r : HRef state.H (.array E)),
        reached.mem (base r.id).val = machine.mem (base r.id).val) := by
  obtain ⟨out,nextBase,reached,target,source,hp,current,stack,bases,grows⟩ :=
    target_pending compiled n repr capacity demand
  refine ⟨reached,target,?_⟩
  intro E r
  have retained := (repr.heap.arrays .dyn r).keeps out.ext (prefix_keeps_heap hp) bases
  have before := retained.length rfl
  have after := (current.heap.arrays .dyn (r.wk out.ext)).length rfl
  have address : nextBase (r.wk out.ext).id = base r.id := bases r
  simpa only [address] using after.trans before.symm

end Solidity.Evm.Memory.HorizonObjectAllocating
