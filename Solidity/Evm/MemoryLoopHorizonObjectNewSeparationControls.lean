import Solidity.Evm.MemoryLoopHorizonObjectNewSeparation
import Solidity.Evm.MemoryLoopHorizonObjectCursorControls

/-! An inhabited two-turn control for distinct freshly allocated arrays.
The proof reuses the published complete allocator fixture and checked loop
selection. Its actual run supplies two typed empty arrays with zero headers,
distinct pointer words, cursor 18 and retained stack 77. No initial physical
representation or target observation is assumed as a theorem premise. -/
namespace Solidity.Evm.Memory.HorizonObjectNewSeparationControls

theorem two_fresh_arrays :
    ∃ (C : Contract) (state : State C []) (initial : Machine)
      (compiled : Construction.CompiledLoop 1 (Frag.init []) (.simple (.bool true) : Val C [] .bool)
        (HorizonObjectAllocating.body : Prog C [] [.mem (.array (.prim .uint))]))
      (out : Solidity.Out C state.H []) (nextBase : Nat → Fin W) (reached : Machine)
      (first second : HRef out.st.H (.array (.prim .uint))),
      Construction.compileLoop 1 (Frag.init []) (.simple (.bool true) : Val C [] .bool)
        (HorizonObjectAllocating.body : Prog C [] [.mem (.array (.prim .uint))]) = some compiled ∧
      state.H = [] ∧ initial.stack = [w[77]] ∧
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        2 initial = .inl reached ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) HorizonObjectAllocating.body state out 2 2 ∧
      first.id = 0 ∧ second.id = 1 ∧
      out.st.heap.len first .dyn = 0 ∧ out.st.heap.len second .dyn = 0 ∧
      reached.mem (nextBase first.id).val = w[0] ∧
      reached.mem (nextBase second.id).val = w[0] ∧
      nextBase first.id ≠ nextBase second.id ∧
      reached.mem 0 = w[18] ∧ reached.stack = [w[77]] := by
  obtain ⟨C,state,base,initial,compiled,oldOut,oldBase,reached,accepted,initialRepr,initialAllocator,
    empty,initialStack,target,source,hp,current,allocator,cursor,stack⟩ :=
    HorizonObjectCursorControls.bounded_execution 2 (by decide)
  obtain ⟨out,nextBase,newReached,newTarget,newPrefix,inventory,separated,oldSeparated⟩ :=
    HorizonObjectAllocating.target_new_array_separation compiled 2 initialRepr
      (by change 1 + 1 ≤ 8; omega)
      (.inr ⟨by decide,_,initialAllocator,by decide⟩)
  have same : newReached = reached := Sum.inl.inj (newTarget.symm.trans target)
  subst newReached
  obtain ⟨first,firstId,firstEmpty,firstHeader⟩ := inventory 0 (by decide)
  obtain ⟨second,secondId,secondEmpty,secondHeader⟩ := inventory 1 (by decide)
  have firstZero : first.id = 0 := by
    simpa only [empty,List.length_nil,Nat.zero_add] using firstId
  have secondOne : second.id = 1 := by
    simpa only [empty,List.length_nil,Nat.zero_add] using secondId
  have distinct : nextBase first.id ≠ nextBase second.id := by
    rw [firstId,secondId]
    exact separated 0 1 (by decide) (by decide) (by decide)
  exact ⟨C,state,initial,compiled,out,nextBase,reached,first,second,accepted,empty,initialStack,
    target,newPrefix,firstZero,secondOne,firstEmpty,secondEmpty,firstHeader,secondHeader,
    distinct,cursor,stack⟩

end Solidity.Evm.Memory.HorizonObjectNewSeparationControls
