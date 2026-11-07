import Solidity.Evm.MemoryLoopHorizonObjectPrefix

/-! Incremental finite capacity for complete-object construction. Shorter
horizons retain room; a successor adds exactly its reached true boundary
demand. A stopped boundary needs no new allocation input. Prefix provenance,
construction cost and strong complete allocator inputs are unchanged. No
unconditional capacity, termination or Source adequacy is inferred. -/
namespace Solidity.Evm.Memory.Construction
variable {C : Contract} {Γ Δ : Ctx}

theorem FiniteLoopRoom.restrict {b frame : Nat} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {horizon limit : Nat}
    (room : FiniteLoopRoom b frame c body σ base m limit) (within : horizon ≤ limit) :
    FiniteLoopRoom b frame c body σ base m horizon := by
  intro o cost turns reached before condition
  exact room o cost turns reached (Nat.lt_of_lt_of_le before within) condition

theorem FiniteLoopRoom.succ_iff {b frame : Nat} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {initial : Machine} {n : Nat} :
    FiniteLoopRoom b frame c body σ base initial (n+1) ↔
      FiniteLoopRoom b frame c body σ base initial n ∧
      (∀ (o : Solidity.Out C σ.H Γ) (cost : Nat),
      CountedLoopPrefix c body σ o cost n → c.evalT o.st=.ok true →
      Objects.AllocationInput b frame (cost+allocationCostProg body o.st) σ base initial) := by
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

end Solidity.Evm.Memory.Construction
