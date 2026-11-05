import Solidity.Evm.MemoryLoopHorizonObservedRoom
import Solidity.Evm.MemoryLoopHorizonControls

/-! Actual iterator observations construct the boundary capacity witness on the
populated aliased-memory fixture. Both condition values consume the observed
zero-turn prefix; the nonallocating body's exact demand is zero. No global
LoopRoom or assumed observation coverage is supplied. -/
namespace Solidity.Evm.Memory.HorizonObservedRoomControls
open CompileExamples

theorem represented (value : Bool) :
    CountedHorizonRelation 1 0 4 (Frag.init Γ) (.simple (.bool value)) HorizonControls.body σ base machine 1
      (TLoop.iterN (horizonBody HorizonControls.body)
        (fun o => (.simple (.bool value) : Val C Γ .bool).evalT o.st) 1 ⟨σ,List.prefix_refl _⟩)
      (loopIterN (fun m => exec (Evm.compileVal 0 (.simple (.bool value) : Val C Γ .bool)) 0 m)
        (fun m => exec [] 0 m) 1 machine) := by
  apply (HorizonControls.cert value).correct_horizon_of_observation_room 1 fixture_repr (by decide +kernel)
  intro turns before o observed condition
  have zero : turns=0 := by omega
  subst turns
  change Sum.inl ⟨σ,List.prefix_refl _⟩=Sum.inl o at observed
  have same := Sum.inl.inj observed
  subst o
  exact ⟨0,.start,.inl rfl⟩

end Solidity.Evm.Memory.HorizonObservedRoomControls
