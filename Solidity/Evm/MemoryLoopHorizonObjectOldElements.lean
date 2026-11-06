import Solidity.Evm.MemoryLoopHorizonObjectAllocatingTarget
import Solidity.Evm.MemoryLoopHorizonObjectHeapKeeps

/-! Physical preservation of live payload cells in original dynamic or fixed
arrays across the actual empty-array allocating loop. Typed word determinism
and transported old-object representations fix primitive values and encoded
reference endpoints. Every observed cell requires a genuine live-element
lookup; arbitrary memory, general stores/copies and capacity are not supplied. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem value_word_unique {H : HTy} {base : Nat → Fin W} {E : Ty} {value : MVal H E}
    {left right : Word} (first : Objects.ValueRepr base E value left)
    (second : Objects.ValueRepr base E value right) : left=right := by
  cases E with
  | prim primitive =>
    cases primitive with
    | uint =>
      rcases first with ⟨a,rfl,ha⟩
      rcases second with ⟨b,rfl,hb⟩
      exact congrArg Word.val (Fin.ext (by omega))
    | bool => exact first.trans second.symm
    | int =>
      rcases first with ⟨a,rfl,ha⟩
      rcases second with ⟨b,rfl,hb⟩
      exact congrArg Word.val (Fin.ext (sgn_inj a.isLt b.isLt (ha.symm.trans hb)))
  | ref reference => exact first.trans second.symm

theorem target_old_array_elements {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame n state base machine) :
    ∃ reached,
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      (∀ (A : RefTy) (E : Ty) (layout : ArrTy A E) (r : HRef state.H A) (i : Nat)
        (value : MVal state.H E), (MObj.elems layout (state.heap.get r))[i]? = some value →
        reached.mem ((base r.id).val + Objects.header layout + i) =
          machine.mem ((base r.id).val + Objects.header layout + i)) := by
  obtain ⟨out,nextBase,reached,target,source,hp,current,stack,bases,grows⟩ :=
    target_pending compiled n repr capacity demand
  refine ⟨reached,target,?_⟩
  intro A E layout r i value live
  have kept : Heap.Keeps out.ext state.heap out.st.heap := prefix_keeps_heap hp
  have retained := (repr.heap.arrays layout r).keeps out.ext kept bases
  have liveAfter : (MObj.elems layout (out.st.heap.get (r.wk out.ext)))[i]? =
      some (MVal.wk out.ext E value) := by
    rw [kept r, MObj.elems_wk, List.getElem?_map, live]
    rfl
  have before := retained.elements i (MVal.wk out.ext E value) liveAfter
  have after := (current.heap.arrays layout (r.wk out.ext)).elements i
    (MVal.wk out.ext E value) liveAfter
  have address : nextBase (r.wk out.ext).id = base r.id := bases r
  simpa only [address] using value_word_unique after before

end Solidity.Evm.Memory.HorizonObjectAllocating
