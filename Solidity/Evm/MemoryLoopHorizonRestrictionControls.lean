import Solidity.Evm.MemoryLoopHorizonRestriction
import Solidity.Evm.MemoryLoopHorizonControls

/-! Both stopping and pending loops on the populated aliased-memory fixture
consume the published counted relation at every horizon below a certified limit.
The fixture is nonallocating; this control does not claim infinite allocator room
for allocating loops. -/
namespace Solidity.Evm.Memory.HorizonRestrictionControls
open CompileExamples

theorem represented (c : Bool) (limit horizon : Nat) (within : horizon ≤ limit) :
    CountedHorizonRelation 1 0 4 (Frag.init Γ) (.simple (.bool c)) HorizonControls.body σ base machine horizon
      (TLoop.iterN (horizonBody HorizonControls.body)
        (fun o => (.simple (.bool c) : Val C Γ .bool).evalT o.st) horizon ⟨σ,List.prefix_refl _⟩)
      (loopIterN (fun m => exec (Evm.compileVal 0 (.simple (.bool c) : Val C Γ .bool)) 0 m)
        (fun m => exec [] 0 m) horizon machine) := by
  exact (HorizonControls.cert c).correct_horizons_le limit fixture_repr (by decide +kernel)
    ((loopRoom_nonallocating (.simple (.bool c)) HorizonControls.body rfl σ base machine).finite limit)
    horizon within

end Solidity.Evm.Memory.HorizonRestrictionControls
