import Solidity.Evm.MemoryLoopHorizonObjectLocalRefLoads
import Solidity.Evm.MemoryLoopHorizonObjectLocalBounds

/-! Exact parent- or child-stage bounds reverts after allocating loops.
A missing parent entry stops the actual composed sequence before the child
read. A genuine parent-child lookup followed by a missing child entry reverts
at the second read. Both stages use the same reached target and original typed
lookups preserved through heap extension. Dynamic/fixed layouts and all child
element types are supported under unchanged strong representation/capacity;
no arbitrary pointer, fault equivalence or rollback claim is made. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem target_nested_array_bounds {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame n state base machine) :
    ∃ (out : Solidity.Out C state.H Γ) (reached : Machine),
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) body state out n n ∧
      (∀ (A R : RefTy) (E : Ty) (parentLayout : ArrTy A (.ref R))
        (childLayout : ArrTy R E) (i : Idx Γ (.mem A)) (parent : HRef state.H A),
        TEnv.get i state.env = some parent →
        ∀ parentIndex childIndex : Fin W,
          ((MObj.elems parentLayout (state.heap.get parent))[parentIndex.val]? = none ∨
            ∃ child, (MObj.elems parentLayout (state.heap.get parent))[parentIndex.val]? = some child ∧
              (MObj.elems childLayout (state.heap.get child))[childIndex.val]? = none) →
          run (([.mload (cellOf b i),.push (.val parentIndex)] ++ Objects.readCode parentLayout) ++
            ([.push (.val childIndex)] ++ Objects.readCode childLayout)) reached = .revert) := by
  obtain ⟨out,nextBase,reached,target,source,hp,current,stack,bases,grows⟩ :=
    target_pending compiled n repr capacity demand
  obtain ⟨refOut,refBase,refReached,refTarget,refPrefix,refBases,reads⟩ :=
    target_local_reference_loads compiled n repr capacity demand
  have refSame : reached = refReached := Sum.inl.inj (target.symm.trans refTarget)
  subst refReached
  obtain ⟨boundOut,boundReached,boundTarget,boundPrefix,bounds⟩ :=
    target_local_array_bounds compiled n repr capacity demand
  have boundSame : reached = boundReached := Sum.inl.inj (target.symm.trans boundTarget)
  subst boundReached
  have kept : Heap.Keeps out.ext state.heap out.st.heap := prefix_keeps_heap hp
  refine ⟨out,reached,target,hp,?_⟩
  intro A R E parentLayout childLayout i parent binding parentIndex childIndex missing
  rcases missing with parentMissing | ⟨child,parentLive,childMissing⟩
  · exact run_append_revert (bounds A (.ref R) parentLayout i parent binding parentIndex parentMissing)
  · have parentLoad := reads A R parentLayout i parent binding parentIndex child parentLive
    have childAfter : (MObj.elems childLayout (out.st.heap.get (HRef.wk out.ext child)))[childIndex.val]? = none := by
      rw [kept child,MObj.elems_wk,List.getElem?_map,childMissing]
      rfl
    have sourceFailure : TRes.ofOpt (out.st.heap.index (HRef.wk out.ext child) childLayout (indexValue childIndex)) =
        .error .revert := by
      simp only [Heap.index,indexValue,Int.toNat_natCast,childAfter,TRes.ofOpt]
    rcases (current.heap.arrays childLayout (HRef.wk out.ext child)).read childIndex with
      ⟨v,word,readValue,represented,load⟩ | ⟨failed,reverted⟩
    · rw [sourceFailure] at readValue
      cases readValue
    · have address : nextBase (HRef.wk out.ext child).id = base child.id := bases child
      rw [address] at reverted
      rw [run_append_ok parentLoad]
      rw [run_append_ok (show run [.push (.val childIndex)] (reached.push (.val (base child.id))) =
        .ok ((reached.push (.val (base child.id))).push (.val childIndex)) 0 by rfl)]
      exact reverted

end Solidity.Evm.Memory.HorizonObjectAllocating
