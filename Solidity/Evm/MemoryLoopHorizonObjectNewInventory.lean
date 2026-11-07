import Solidity.Evm.MemoryLoopHorizonObjectNewArrays
import Solidity.Evm.MemoryLoopHorizonObjectHeapTypes

/-! Inhabited inventory of the actual allocating loop's new uint arrays.
Each turn index below the finite horizon identifies a typed source reference
at the corresponding appended heap position. The same actual reached machine
has a zero header for every such reference. Capacity and complete input
representation remain explicit; no physical address distinctness or layout
beyond the reached representation is inferred. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem prefix_new_ref {state : State C Γ} {out : Solidity.Out C state.H Γ} {cost count : Nat}
    (hp : Construction.CountedLoopPrefix (.simple (.bool true)) body state out cost count)
    (i : Nat) (within : i < count) :
    ∃ r : HRef out.st.H (.array (.prim .uint)),
      r.id = state.H.length + i ∧ out.st.heap.len r .dyn = 0 := by
  have types := prefix_heap_types hp
  have lookup : out.st.H[state.H.length + i]? = some (.array (.prim .uint)) := by
    rw [types, List.getElem?_append_right (by omega)]
    simpa only [Nat.add_sub_cancel_left] using
      (List.getElem?_replicate_of_lt (a := RefTy.array (.prim .uint)) within)
  let r : HRef out.st.H (.array (.prim .uint)) := ⟨state.H.length + i,lookup⟩
  exact ⟨r,rfl,prefix_new_empty hp r (by change state.H.length ≤ state.H.length + i; omega)⟩

theorem target_new_array_inventory {L b frame : Nat}
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
        reached.mem (nextBase r.id).val = w[0]) := by
  obtain ⟨out,nextBase,reached,target,hp,headers⟩ :=
    target_new_array_headers compiled n repr capacity demand
  refine ⟨out,nextBase,reached,target,hp,?_⟩
  intro i within
  obtain ⟨r,identity,empty⟩ := prefix_new_ref hp i within
  exact ⟨r,identity,empty,headers r (by omega)⟩

end Solidity.Evm.Memory.HorizonObjectAllocating
