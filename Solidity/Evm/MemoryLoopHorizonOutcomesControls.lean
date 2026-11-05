import Solidity.Evm.MemoryLoopHorizonOutcomes
import Solidity.Evm.MemoryLoopHorizonRestrictionControls

/-! Outcome consumers use the bounded counted transport on the populated
aliased-memory fixture, for both stopping and pending loops. No fault exclusion
is inferred without its finite capacity/representation certificate. -/
namespace Solidity.Evm.Memory.HorizonOutcomeControls
open CompileExamples

theorem no_fault (c : Bool) (limit horizon : Nat) (within : horizon ≤ limit) :
    loopIterN (fun m => exec (Evm.compileVal 0 (.simple (.bool c) : Val C Γ .bool)) 0 m)
      (fun m => exec [] 0 m) horizon machine≠.inr .fault := by
  exact (HorizonRestrictionControls.represented c limit horizon within).no_fault

theorem pending_agreement (c : Bool) (limit horizon : Nat) (within : horizon ≤ limit) :
    (∃ o, TLoop.iterN (horizonBody HorizonControls.body)
      (fun o => (.simple (.bool c) : Val C Γ .bool).evalT o.st) horizon ⟨σ,List.prefix_refl _⟩=.inl o) ↔
    (∃ reached, loopIterN (fun m => exec (Evm.compileVal 0 (.simple (.bool c) : Val C Γ .bool)) 0 m)
      (fun m => exec [] 0 m) horizon machine=.inl reached) := by
  exact (HorizonRestrictionControls.represented c limit horizon within).pending_iff

end Solidity.Evm.Memory.HorizonOutcomeControls
