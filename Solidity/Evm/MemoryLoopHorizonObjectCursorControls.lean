import Solidity.Evm.MemoryLoopHorizonObjectAllocatingTarget
import Solidity.Evm.MemoryLoopHorizonObjectCompileAllocating
import Solidity.Evm.MemoryObjectConstructionExamples

/-! Existentially witnessed target observations for selected allocating loops.
The proof chooses the published ConstructionExamples fixture, while the theorem
quantifies over the state, base and initial machine. Under 16+n<W it retains
Objects.StateRepr and Objects.AllocatorRepr, with a pending target, cursor cell
16+n and stack 77. No assumed target observation or general capacity is supplied. -/
namespace Solidity.Evm.Memory.HorizonObjectCursorControls

theorem bounded_execution (n : Nat) (space : 16+n < W) :
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
      Objects.AllocatorRepr out.st.heap nextBase 8 ⟨16+n,space⟩ reached ∧
      reached.mem 0 = .val ⟨16+n,space⟩ ∧ reached.stack=[w[77]] := by
  obtain ⟨compiled,accepted,_transport⟩ := HorizonObjectCompileAllocating.represented n
    ConstructionExamples.initial_repr (by change 1 + 1 ≤ 8; omega)
    (.inr ⟨by decide,_,ConstructionExamples.initial_allocator,space⟩)
  obtain ⟨out,nextBase,reached,target,source,hp,current,stack,_bases,allocator⟩ :=
    HorizonObjectAllocating.target_allocator compiled n ConstructionExamples.initial_repr
      (by change 1 + 1 ≤ 8; omega) (by decide) ConstructionExamples.initial_allocator space
  refine ⟨_,_,_,_,compiled,out,nextBase,reached,accepted,ConstructionExamples.initial_repr,ConstructionExamples.initial_allocator,rfl,rfl,target,source,hp,current,
    allocator,allocator.free.cell,?_⟩
  exact stack

end Solidity.Evm.Memory.HorizonObjectCursorControls
