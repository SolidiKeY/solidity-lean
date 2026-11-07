import Solidity.Evm.MemoryLoopHorizonObjectCursorControls
import Solidity.Evm.MemoryLoopHorizonObjectHeapGrowth

/-! Existentially witnessed selected-loop execution with matched object count
and cursor observations. Genuine source-prefix heap growth adds exactly n
objects to the published empty heap; the same selected run retains complete
allocator ownership, cursor cell 16+n and stack 77 under 16+n<W. No source
heap count is inferred merely from allocation cost, and no general capacity
or unbounded target execution is supplied. -/
namespace Solidity.Evm.Memory.HorizonObjectHeapControls

theorem bounded_heap_execution (n : Nat) (space : 16+n < W) :
    ∃ (C : Contract) (state : State C []) (base : Nat → Fin W) (initial : Machine)
      (compiled : Construction.CompiledLoop 1 (Frag.init []) (.simple (.bool true) : Val C [] .bool)
        (HorizonObjectAllocating.body : Prog C [] [.mem (.array (.prim .uint))]))
      (out : Solidity.Out C state.H []) (nextBase : Nat → Fin W) (reached : Machine),
      Construction.compileLoop 1 (Frag.init []) (.simple (.bool true) : Val C [] .bool)
        (HorizonObjectAllocating.body : Prog C [] [.mem (.array (.prim .uint))]) = some compiled ∧
      Objects.StateRepr 1 1 8 (Frag.init []) state base initial ∧
      Objects.AllocatorRepr state.heap base 8 ⟨16,by decide⟩ initial ∧
      state.H=[] ∧ initial.stack=[w[77]] ∧
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n initial = .inl reached ∧
      TLoop.iterN (horizonBody HorizonObjectAllocating.body)
        (fun o => (.simple (.bool true) : Val C [] .bool).evalT o.st) n
        ⟨state,List.prefix_refl _⟩ = .inl out ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) HorizonObjectAllocating.body state out n n ∧
      Objects.StateRepr 1 1 8 (Frag.init []) out.st nextBase reached ∧
      out.st.H.length=n ∧
      Objects.AllocatorRepr out.st.heap nextBase 8 ⟨16+n,space⟩ reached ∧
      reached.mem 0 = .val ⟨16+n,space⟩ ∧ reached.stack=[w[77]] := by
  obtain ⟨C,state,base,initial,compiled,out,nextBase,reached,accepted,initialRepr,initialAllocator,
    empty,initialStack,target,source,hp,current,allocator,cursor,stack⟩ :=
    HorizonObjectCursorControls.bounded_execution n space
  refine ⟨C,state,base,initial,compiled,out,nextBase,reached,accepted,initialRepr,initialAllocator,
    empty,initialStack,target,source,hp,current,?_,allocator,cursor,stack⟩
  have count := HorizonObjectAllocating.prefix_heap_length hp
  simpa only [empty, List.length_nil, Nat.zero_add] using count

end Solidity.Evm.Memory.HorizonObjectHeapControls
