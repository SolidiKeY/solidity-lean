import Solidity.Evm.MemoryLoopHorizonObjectLocalAlias
import Solidity.Evm.MemoryLoopHorizonObjectOldElements

/-! Reads through actual initialized array locals after allocating loops.
The same reached execution preserves each local binding and stored pointer;
its live source elements survive with the actual heap-extension weakening.
Target payload words agree at the retained pointer, for dynamic or fixed
arrays and primitive or reference elements. A genuine initialized binding and
live-element lookup are required. Capacity, representation and exclusions
remain unchanged; no arbitrary memory or mutating-loop read claim is made. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem target_local_array_reads {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame n state base machine) :
    ∃ (out : Solidity.Out C state.H Γ) (nextBase : Nat → Fin W) (reached : Machine),
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) body state out n n ∧
      (∀ (A : RefTy) (E : Ty) (layout : ArrTy A E) (i : Idx Γ (.mem A))
        (r : HRef state.H A), TEnv.get i state.env = some r →
        TEnv.get i out.st.env = some (r.wk out.ext) ∧
        reached.mem (cellOf b i) = machine.mem (cellOf b i) ∧
        (∀ k (value : MVal state.H E),
          (MObj.elems layout (state.heap.get r))[k]? = some value →
          (MObj.elems layout (out.st.heap.get (r.wk out.ext)))[k]? =
            some (MVal.wk out.ext E value) ∧
          reached.mem ((nextBase (r.wk out.ext).id).val + Objects.header layout + k) =
            machine.mem ((base r.id).val + Objects.header layout + k))) := by
  obtain ⟨out,nextBase,reached,target,hp,locals⟩ :=
    target_local_aliases compiled n repr capacity demand
  obtain ⟨elementReached,elementTarget,elements⟩ :=
    target_old_array_elements compiled n repr capacity demand
  have same : reached = elementReached := Sum.inl.inj (target.symm.trans elementTarget)
  subst elementReached
  have kept : Heap.Keeps out.ext state.heap out.st.heap := prefix_keeps_heap hp
  refine ⟨out,nextBase,reached,target,hp,?_⟩
  intro A E layout i r binding
  obtain ⟨finalBinding,address,localWord⟩ := locals i r binding
  refine ⟨finalBinding,localWord,?_⟩
  intro k value live
  constructor
  · rw [kept r,MObj.elems_wk,List.getElem?_map,live]
    rfl
  · rw [address]
    exact elements A E layout r k value live

end Solidity.Evm.Memory.HorizonObjectAllocating
