import Solidity.Evm.MemoryLoopHorizonObjectCompileAllocating
import Solidity.Evm.MemoryObjectConstructionExamples

/-! A concrete complete allocator at cursor 16 instantiates actual checked
allocating-loop transport for every horizon with 16+horizon<W. The initial
strong representation and allocator come from the published construction
fixture; no private fixture definitions or substitute producers are copied.
This bounded inhabitant is not general capacity or unbounded loop execution. -/
namespace Solidity.Evm.Memory.HorizonObjectCapacityControls

theorem bounded_horizons (horizon : Nat) (space : 16 + horizon < W) :
    ∃ (C : Contract) (state : State C []) (base : Nat → Fin W) (machine : Machine)
      (compiled : Construction.CompiledLoop 1 (Frag.init []) (.simple (.bool true) : Val C [] .bool)
        (HorizonObjectAllocating.body : Prog C [] [.mem (.array (.prim .uint))])),
      Construction.compileLoop 1 (Frag.init []) (.simple (.bool true) : Val C [] .bool)
        (HorizonObjectAllocating.body : Prog C [] [.mem (.array (.prim .uint))]) = some compiled ∧
      Objects.StateRepr 1 1 8 (Frag.init []) state base machine ∧
      Objects.AllocatorRepr state.heap base 8 ⟨16,by decide⟩ machine ∧
      Construction.CountedHorizonRelation 1 1 8 (Frag.init []) (.simple (.bool true))
        HorizonObjectAllocating.body state base machine horizon
        (TLoop.iterN (horizonBody HorizonObjectAllocating.body)
          (fun o => (.simple (.bool true) : Val C [] .bool).evalT o.st)
          horizon ⟨state,List.prefix_refl _⟩)
        (loopIterN (fun m => exec compiled.conditionCode 0 m)
          (fun m => exec compiled.bodyCode 0 m) horizon machine) ∧
      state.H=[] ∧ machine.stack=[w[77]] ∧ machine.mem 0=w[16] := by
  obtain ⟨compiled,accepted,transport⟩ := HorizonObjectCompileAllocating.represented horizon
    ConstructionExamples.initial_repr (by decide +kernel)
    (.inr ⟨by decide,_,ConstructionExamples.initial_allocator,space⟩)
  exact ⟨_,_,_,_,compiled,accepted,ConstructionExamples.initial_repr,
    ConstructionExamples.initial_allocator,transport,rfl,rfl,rfl⟩

end Solidity.Evm.Memory.HorizonObjectCapacityControls
