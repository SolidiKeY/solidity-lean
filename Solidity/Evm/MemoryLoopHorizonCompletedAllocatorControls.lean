import Solidity.Evm.MemoryLoopHorizonCompletedAllocator
import Solidity.Evm.MemoryLoopHorizonCompletedControls
import Solidity.Evm.MemoryLoopHorizonCapacityControls

/-! The actual completed stopped fixture takes no successful body turns and
incurs zero allocation cost. Its represented final state is extracted through
the completed allocator consumer, without asserting an allocator at zero cost.
Positive-cost allocator realization is covered by the generic checked proof. -/
namespace Solidity.Evm.Memory.HorizonCompletedAllocatorControls
open CompileExamples

theorem stop_zero_prefix :
    ∃ (o : Solidity.Out C σ.H Γ) (nextBase : Nat → Fin W),
      TLoop.iterN (horizonBody HorizonControls.body) (fun o => HorizonControls.stop.evalT o.st) 1
        ⟨σ,List.prefix_refl _⟩=.inr (.ok o) ∧
      CountedLoopPrefix HorizonControls.stop HorizonControls.body σ o 0 0 ∧
      StateRepr 1 0 4 (Frag.init Γ) o.st nextBase machine := by
  obtain ⟨o,nextBase,cost,count,observed,hp,earlier,stopped,current,stack,bases,grows,allocator⟩ :=
    (HorizonControls.cert false).completed_allocator 1 fixture_repr (by decide +kernel)
      HorizonCapacityControls.stop_room_one HorizonCompletedControls.stop_target_one
  have zero : count=0 := by omega
  subst count
  cases hp
  exact ⟨_,nextBase,observed,.start,current⟩

end Solidity.Evm.Memory.HorizonCompletedAllocatorControls
