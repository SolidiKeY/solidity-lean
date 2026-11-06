import Solidity.Evm.MemoryLoopHorizonObjectLocalAlias
import Solidity.Evm.MemoryLoopHorizonObjectHeapKeeps

/-! Exact bounds reverts for loads through retained initialized array locals.
A missing source lookup remains missing through actual loop heap extension.
The executed pointer load, word-sized index push and owner read sequence then
revert for either array layout and any element type. No arbitrary fault or
transaction rollback claim is made; initialized bindings, missing lookups,
complete representation and finite capacity remain explicit. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem target_local_array_bounds {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame n state base machine) :
    ∃ (out : Solidity.Out C state.H Γ) (reached : Machine),
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) body state out n n ∧
      (∀ (A : RefTy) (E : Ty) (layout : ArrTy A E)
        (i : Idx Γ (.mem A)) (r : HRef state.H A), TEnv.get i state.env = some r →
        ∀ index : Fin W, (MObj.elems layout (state.heap.get r))[index.val]? = none →
          run ([.mload (cellOf b i), .push (.val index)] ++ Objects.readCode layout) reached = .revert) := by
  obtain ⟨out,nextBase,reached,target,source,hp,current,stack,bases,grows⟩ :=
    target_pending compiled n repr capacity demand
  have kept : Heap.Keeps out.ext state.heap out.st.heap := prefix_keeps_heap hp
  refine ⟨out,reached,target,hp,?_⟩
  intro A E layout i r binding index missing
  have finalBinding := prefix_local_ref hp i r binding
  obtain ⟨q,qBinding,localWord⟩ := current.pointers i
  have sameRef : r.wk out.ext = q := Option.some.inj (finalBinding.symm.trans qBinding)
  subst q
  have missingAfter : (MObj.elems layout (out.st.heap.get (r.wk out.ext)))[index.val]? = none := by
    rw [kept r,MObj.elems_wk,List.getElem?_map,missing]
    rfl
  have sourceFailure : TRes.ofOpt (out.st.heap.index (r.wk out.ext) layout (indexValue index)) =
      .error .revert := by
    simp only [Heap.index,indexValue,Int.toNat_natCast,missingAfter,TRes.ofOpt]
  have localRun : run [.mload (cellOf b i)] reached =
      .ok (reached.push (.val (nextBase (r.wk out.ext).id))) 0 := by
    change Out.ok (reached.push (reached.mem (cellOf b i))) 0 = _
    rw [localWord]
  rcases (current.heap.arrays layout (r.wk out.ext)).read index with
    ⟨v,word,readValue,represented,load⟩ | ⟨failed,reverted⟩
  · rw [sourceFailure] at readValue
    cases readValue
  · change run ([.mload (cellOf b i)] ++ ([.push (.val index)] ++ Objects.readCode layout)) reached = _
    rw [run_append_ok localRun]
    rw [run_append_ok (show run [.push (.val index)]
      (reached.push (.val (nextBase (r.wk out.ext).id))) =
      .ok ((reached.push (.val (nextBase (r.wk out.ext).id))).push (.val index)) 0 by rfl)]
    exact reverted

end Solidity.Evm.Memory.HorizonObjectAllocating
