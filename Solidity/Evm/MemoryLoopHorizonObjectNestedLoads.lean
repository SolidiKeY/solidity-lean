import Solidity.Evm.MemoryLoopHorizonObjectLocalRefLoads

/-! Actual nested loads through a retained parent local after loop allocation.
The first read obtains the original typed child pointer from the parent;
the second uses that returned pointer to read a live primitive child element.
Both source lookups and heap-extension weakening are genuine. Dynamic/fixed
layouts compose through their existing bounds/address code, with the original
strong representation and finite allocation demand. No child local, arbitrary
pointer or frontend selection is assumed. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem target_nested_array_loads {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame n state base machine) :
    ∃ (out : Solidity.Out C state.H Γ) (reached : Machine),
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) body state out n n ∧
      (∀ (A R : RefTy) (p : PrimTy) (parentLayout : ArrTy A (.ref R))
        (childLayout : ArrTy R (.prim p)) (i : Idx Γ (.mem A)) (parent : HRef state.H A),
        TEnv.get i state.env = some parent →
        ∀ (parentIndex childIndex : Fin W) (child : HRef state.H R) (value : MVal state.H (.prim p)),
          (MObj.elems parentLayout (state.heap.get parent))[parentIndex.val]? = some child →
          (MObj.elems childLayout (state.heap.get child))[childIndex.val]? = some value →
          ∃ word, ReprV p value word ∧
            run (([.mload (cellOf b i),.push (.val parentIndex)] ++ Objects.readCode parentLayout) ++
              ([.push (.val childIndex)] ++ Objects.readCode childLayout)) reached =
              .ok (reached.push word) 0) := by
  obtain ⟨out,nextBase,reached,target,source,hp,current,stack,bases,grows⟩ :=
    target_pending compiled n repr capacity demand
  obtain ⟨refOut,refBase,refReached,refTarget,refPrefix,refBases,reads⟩ :=
    target_local_reference_loads compiled n repr capacity demand
  have same : reached = refReached := Sum.inl.inj (target.symm.trans refTarget)
  subst refReached
  have kept : Heap.Keeps out.ext state.heap out.st.heap := prefix_keeps_heap hp
  refine ⟨out,reached,target,hp,?_⟩
  intro A R p parentLayout childLayout i parent binding parentIndex childIndex child value parentLive childLive
  have parentLoad := reads A R parentLayout i parent binding parentIndex child parentLive
  have childAfter : (MObj.elems childLayout (out.st.heap.get (child.wk out.ext)))[childIndex.val]? =
      some (MVal.wk out.ext (.prim p) value) := by
    rw [kept child,MObj.elems_wk,List.getElem?_map,childLive]
    rfl
  have sourceValue : TRes.ofOpt (out.st.heap.index (child.wk out.ext) childLayout (indexValue childIndex)) =
      .ok (MVal.wk out.ext (.prim p) value) := by
    simp only [Heap.index,indexValue,Int.toNat_natCast,childAfter,TRes.ofOpt]
  rcases (current.heap.arrays childLayout (child.wk out.ext)).read childIndex with
    ⟨v,word,readValue,represented,load⟩ | ⟨failed,reverted⟩
  · rw [sourceValue] at readValue
    cases readValue
    refine ⟨word,represented,?_⟩
    have address : nextBase (child.wk out.ext).id = base child.id := bases child
    rw [address] at load
    rw [run_append_ok parentLoad]
    rw [run_append_ok (show run [.push (.val childIndex)] (reached.push (.val (base child.id))) =
      .ok ((reached.push (.val (base child.id))).push (.val childIndex)) 0 by rfl)]
    exact load
  · rw [sourceValue] at failed
    cases failed

end Solidity.Evm.Memory.HorizonObjectAllocating
