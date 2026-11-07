import Solidity.Evm.MemoryLoopHorizonObjectNestedLoads
import Solidity.Evm.MemoryLoopHorizonObjectNestedBounds
import Solidity.Evm.MemoryLoopHorizonObjectOldElements
import Solidity.Evm.MemoryObjectArrayExamples

/-! Inhabited nested read success and two bounds-failure stages.
The published populated fixed-parent fixture and complete cursor40 input
supply the actual source objects. One loop-reached machine returns primitive7
through parent index0/child index0, reverts at missing parent index2, and
reverts at missing child index1. The target obtains the child pointer from the
parent; no child-local or target-observation premise is assumed. Only finite
word-space remains explicit; checked selection and rollback are not claimed. -/
namespace Solidity.Evm.Memory.HorizonObjectNestedControls

def nestedCode {Γ : Ctx} (b : Nat)
    (i : Idx Γ (.mem (.fixed (.ref (.array (.prim .uint))) 2)))
    (parentIndex childIndex : Fin W) : List Instr :=
  ([.mload (cellOf b i),.push (.val parentIndex)] ++ Objects.readCode
    (ArrTy.fixed : ArrTy (.fixed (.ref (.array (.prim .uint))) 2) (.ref (.array (.prim .uint))))) ++
  ([.push (.val childIndex)] ++ Objects.readCode (ArrTy.dyn : ArrTy (.array (.prim .uint)) (.prim .uint)))

theorem populated_nested_outcomes (n : Nat) (space : 40 + n < W) :
    ∃ (C : Contract) (Γ : Ctx) (state : State C Γ) (initial : Machine)
      (compiled : Construction.CompiledLoop 1 (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool)
        (HorizonObjectAllocating.body : Prog C Γ (.mem (.array (.prim .uint))::Γ)))
      (out : Solidity.Out C state.H Γ) (reached : Machine)
      (i : Idx Γ (.mem (.fixed (.ref (.array (.prim .uint))) 2))),
      state.H.length = 3 ∧
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n initial = .inl reached ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) HorizonObjectAllocating.body state out n n ∧
      run (nestedCode 1 i (wmod 0) (wmod 0)) reached = .ok (reached.push w[7]) 0 ∧
      run (nestedCode 1 i (wmod 2) (wmod 0)) reached = .revert ∧
      run (nestedCode 1 i (wmod 0) (wmod 1)) reached = .revert := by
  obtain ⟨out,reached,target,hp,reads⟩ :=
    HorizonObjectAllocating.target_nested_array_loads
      ⟨_,_,HorizonObjectAllocating.cert 1 (by decide)⟩ n
      ObjectArrayExamples.initial_repr (by change 1 + 4 ≤ 8; omega)
      (.inr ⟨by decide,_,ObjectArrayExamples.initial_allocator,space⟩)
  obtain ⟨boundOut,boundReached,boundTarget,boundPrefix,bounds⟩ :=
    HorizonObjectAllocating.target_nested_array_bounds
      ⟨_,_,HorizonObjectAllocating.cert 1 (by decide)⟩ n
      ObjectArrayExamples.initial_repr (by change 1 + 4 ≤ 8; omega)
      (.inr ⟨by decide,_,ObjectArrayExamples.initial_allocator,space⟩)
  have same : reached = boundReached := Sum.inl.inj (target.symm.trans boundTarget)
  subst boundReached
  obtain ⟨word,represented,good⟩ := reads _ _ .uint .fixed .dyn .here _ rfl (wmod 0) (wmod 0) _ _
    (by rw [MObj.elems_fixed]; rfl) (by rw [MObj.elems_dyn]; rfl)
  have wordSeven : word = w[7] := HorizonObjectAllocating.value_word_unique (H := []) (base := fun _ => wmod 0)
    (E := .prim .uint) represented (ReprV.uint_of rfl)
  rw [wordSeven] at good
  have parentBad := bounds _ _ (.prim .uint) .fixed .dyn .here _ rfl (wmod 2) (wmod 0)
    (.inl (by rw [MObj.elems_fixed]; rfl))
  have childBad := bounds _ _ (.prim .uint) .fixed .dyn .here _ rfl (wmod 0) (wmod 1)
    (.inr ⟨_,by rw [MObj.elems_fixed]; rfl,by rw [MObj.elems_dyn]; rfl⟩)
  exact ⟨_,_,_,_,_,out,reached,.here,rfl,target,hp,good,parentBad,childBad⟩

end Solidity.Evm.Memory.HorizonObjectNestedControls
