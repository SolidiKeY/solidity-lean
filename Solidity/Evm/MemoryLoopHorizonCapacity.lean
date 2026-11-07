import Solidity.Evm.MemoryLoopHorizonRestriction

/-! Exact incremental construction of the published finite-capacity contract.
A successor horizon adds only its reached true-condition boundary demand.
If that boundary has stopped, no new allocation input is needed. Cost, prefix
provenance and initial allocator remain the existing owner definitions; no
capacity bound or termination assumption is invented. -/
namespace Solidity.Evm.Memory
variable {C : Contract} {Γ Δ : Ctx}

theorem FiniteLoopRoom.succ_iff {b frame : Nat} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {initial : Machine} {n : Nat} :
    FiniteLoopRoom b frame c body σ base initial (n+1) ↔
      FiniteLoopRoom b frame c body σ base initial n ∧
      (∀ (o : Solidity.Out C σ.H Γ) (cost : Nat),
      CountedLoopPrefix c body σ o cost n → c.evalT o.st=.ok true →
      AllocationInput b frame (cost+allocationCostProg body o.st) σ base initial) := by
  constructor
  · intro room
    exact ⟨room.restrict (by omega),fun o cost hp hc => room o cost n hp (by omega) hc⟩
  · rintro ⟨room,boundary⟩ o cost turns hp before condition
    by_cases earlier : turns<n
    · exact room o cost turns hp earlier condition
    · have same : turns=n := by omega
      subst turns
      exact boundary o cost hp condition

theorem FiniteLoopRoom.succ_of_stopped {b frame : Nat} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {initial : Machine} {n : Nat}
    (room : FiniteLoopRoom b frame c body σ base initial n)
    (stopped : ∀ (o : Solidity.Out C σ.H Γ) (cost : Nat),
      CountedLoopPrefix c body σ o cost n → c.evalT o.st=.ok false) :
    FiniteLoopRoom b frame c body σ base initial (n+1) := by
  apply FiniteLoopRoom.succ_iff.mpr
  refine ⟨room,?_⟩
  intro o cost hp condition
  rw [stopped o cost hp] at condition
  cases condition

end Solidity.Evm.Memory
