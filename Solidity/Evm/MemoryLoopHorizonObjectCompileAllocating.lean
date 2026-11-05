import Solidity.Evm.MemoryLoopHorizonObjectCompile
import Solidity.Evm.MemoryLoopHorizonObjectAllocating

/-! Actual checked selection of the existing empty-array allocating body. The
returned owner-composed strong certificate transports its actual emitted code
under explicit frame and complete allocator demand for the finite horizon.
Acceptance is proved, but no physical capacity witness, recursive-body support
or full compiler-selection/Source adequacy closure is supplied. -/
namespace Solidity.Evm.Memory.HorizonObjectCompileAllocating
variable {C : Contract}

theorem selected : ∃ compiled,
    Construction.compileLoop 1 (Frag.init []) (.simple (.bool true) : Val C [] .bool)
        (HorizonObjectAllocating.body : Prog C [] [.mem (.array (.prim .uint))]) = some compiled := by
  exact ⟨_,rfl⟩

theorem represented {L frame : Nat} {state : State C []} {base : Nat → Fin W}
    {machine : Machine} (horizon : Nat)
    (repr : Objects.StateRepr L 1 frame (Frag.init []) state base machine)
    (capacity : 1 + frameNeedProg (HorizonObjectAllocating.body : Prog C [] _) ≤ frame)
    (demand : Objects.AllocationInput 1 frame horizon state base machine) :
    ∃ compiled,
      Construction.compileLoop 1 (Frag.init []) (.simple (.bool true) : Val C [] .bool)
        (HorizonObjectAllocating.body : Prog C [] [.mem (.array (.prim .uint))]) = some compiled ∧
      Construction.CountedHorizonRelation L 1 frame (Frag.init []) (.simple (.bool true))
        HorizonObjectAllocating.body state base machine horizon
        (TLoop.iterN (horizonBody HorizonObjectAllocating.body)
          (fun o => (.simple (.bool true) : Val C [] .bool).evalT o.st)
          horizon ⟨state,List.prefix_refl _⟩)
        (loopIterN (fun m => exec compiled.conditionCode 0 m)
          (fun m => exec compiled.bodyCode 0 m) horizon machine) := by
  obtain ⟨compiled,accepted⟩ := selected (C:=C)
  exact ⟨compiled,accepted,compiled.correct_finite_horizon horizon repr capacity
    (HorizonObjectAllocating.room horizon demand)⟩

end Solidity.Evm.Memory.HorizonObjectCompileAllocating
