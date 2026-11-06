import Solidity.Evm.MemoryLoopHorizonObjectNewInventory
import Solidity.Evm.MemoryObjectFrame

/-! Pointer separation for actual finite allocating loop executions.
Every turn-indexed new empty array has a zero header in the same reached
machine. Positive ownership reservations distinguish different new arrays
and separate their pointers from every original typed object. All existing
strong representation, frame, and allocation-demand premises are retained. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem target_new_array_separation {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame n state base machine) :
    ∃ (out : Solidity.Out C state.H Γ) (nextBase : Nat → Fin W) (reached : Machine),
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) body state out n n ∧
      (∀ i, i < n → ∃ r : HRef out.st.H (.array (.prim .uint)),
        r.id = state.H.length + i ∧ out.st.heap.len r .dyn = 0 ∧
        reached.mem (nextBase r.id).val = w[0]) ∧
      (∀ i j, i < n → j < n → i ≠ j →
        nextBase (state.H.length + i) ≠ nextBase (state.H.length + j)) ∧
      (∀ i, i < n → ∀ {R : RefTy} (old : HRef state.H R),
        nextBase (state.H.length + i) ≠ base old.id) := by
  obtain ⟨out,nextBase,reached,target,source,hp,current,stack,bases,grows⟩ :=
    target_pending compiled n repr capacity demand
  refine ⟨out,nextBase,reached,target,hp,?_,?_,?_⟩
  · intro i within
    obtain ⟨r,identity,empty⟩ := prefix_new_ref hp i within
    have header := (current.heap.arrays .dyn r).length rfl
    exact ⟨r,identity,empty,by simpa only [empty] using header⟩
  · intro i j hi hj different equal
    obtain ⟨r,ri,emptyR⟩ := prefix_new_ref hp i hi
    obtain ⟨q,qj,emptyQ⟩ := prefix_new_ref hp j hj
    have sameBase : nextBase r.id = nextBase q.id := by
      simpa only [ri,qj] using equal
    have sameId := current.heap.owner.base_injective r q sameBase
    exact different (by omega)
  · intro i within R old equal
    obtain ⟨r,identity,empty⟩ := prefix_new_ref hp i within
    have sameBase : nextBase r.id = nextBase (old.wk out.ext).id := by
      change nextBase r.id = nextBase old.id
      rw [identity,bases old]
      exact equal
    have sameId := current.heap.owner.base_injective r (old.wk out.ext) sameBase
    have oldBound := old.id_lt
    change r.id = old.id at sameId
    omega

end Solidity.Evm.Memory.HorizonObjectAllocating
