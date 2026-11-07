import Solidity.Evm.MemoryLoopHorizonObjectLocalRefLoads
import Solidity.Evm.MemoryLoopHorizonObjectLocalBounds
import Solidity.Evm.MemoryObjectArrayExamples

/-! Inhabited success and bounds-revert observations after allocating loops.
The public three-object fixed-parent fixture and complete cursor40 allocator
supply real input. From the same actual reached loop state, a local parent
read at index0 returns child pointer16 and a read at index2 reverts. Owner-
composed loop certificates and existing read laws are reused; the only premise
is finite word-space. No checked selection or rollback claim is introduced. -/
namespace Solidity.Evm.Memory.HorizonObjectLocalLoadControls

theorem populated_read_outcomes (n : Nat) (space : 40 + n < W) :
    ∃ (C : Contract) (Γ : Ctx) (state : State C Γ) (initial : Machine)
      (compiled : Construction.CompiledLoop 1 (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool)
        (HorizonObjectAllocating.body : Prog C Γ (.mem (.array (.prim .uint))::Γ)))
      (out : Solidity.Out C state.H Γ) (reached : Machine)
      (i : Idx Γ (.mem (.fixed (.ref (.array (.prim .uint))) 2))),
      state.H.length = 3 ∧
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n initial = .inl reached ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) HorizonObjectAllocating.body state out n n ∧
      run ([.mload (cellOf 1 i),.push w[0]] ++
        Objects.readCode (ArrTy.fixed : ArrTy (.fixed (.ref (.array (.prim .uint))) 2) (.ref (.array (.prim .uint)))))
        reached = .ok (reached.push w[16]) 0 ∧
      run ([.mload (cellOf 1 i),.push w[2]] ++
        Objects.readCode (ArrTy.fixed : ArrTy (.fixed (.ref (.array (.prim .uint))) 2) (.ref (.array (.prim .uint)))))
        reached = .revert := by
  obtain ⟨out,nextBase,reached,target,hp,bases,reads⟩ :=
    HorizonObjectAllocating.target_local_reference_loads
      ⟨_,_,HorizonObjectAllocating.cert 1 (by decide)⟩ n
      ObjectArrayExamples.initial_repr (by change 1 + 4 ≤ 8; omega)
      (.inr ⟨by decide,_,ObjectArrayExamples.initial_allocator,space⟩)
  obtain ⟨boundOut,boundReached,boundTarget,boundPrefix,bounds⟩ :=
    HorizonObjectAllocating.target_local_array_bounds
      ⟨_,_,HorizonObjectAllocating.cert 1 (by decide)⟩ n
      ObjectArrayExamples.initial_repr (by change 1 + 4 ≤ 8; omega)
      (.inr ⟨by decide,_,ObjectArrayExamples.initial_allocator,space⟩)
  have same : reached = boundReached := Sum.inl.inj (target.symm.trans boundTarget)
  subst boundReached
  have good := reads _ _ .fixed .here _ rfl (wmod 0) _ (by rw [MObj.elems_fixed]; rfl)
  have bad := bounds _ _ .fixed .here _ rfl (wmod 2) (by rw [MObj.elems_fixed]; rfl)
  exact ⟨_,_,_,_,_,out,reached,.here,rfl,target,hp,good,bad⟩

end Solidity.Evm.Memory.HorizonObjectLocalLoadControls
