import Solidity.Evm.MemoryLoopHorizonCost

/-! Finite capacity characterized by actual pending source observations. The
existential boundary cost must be witnessed by a genuine counted prefix; cost
uniqueness aligns it with every required prefix. Thus the adapter assumes no
trace coverage or output simulation law and retains the owner's full initial
allocator/frame demand, including allocating turns that later revert. -/
namespace Solidity.Evm.Memory
variable {C : Contract} {Γ Δ : Ctx}

theorem finiteLoopRoom_iff_observations {b frame : Nat} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {initial : Machine} {horizon : Nat} :
    FiniteLoopRoom b frame c body σ base initial horizon ↔
    (∀ (turns : Nat), turns < horizon → ∀ (o : Solidity.Out C σ.H Γ),
      TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) turns ⟨σ,List.prefix_refl _⟩=.inl o →
      c.evalT o.st=.ok true → ∃ cost, CountedLoopPrefix c body σ o cost turns ∧
        AllocationInput b frame (cost+allocationCostProg body o.st) σ base initial) := by
  constructor
  · intro room turns before o observed condition
    obtain ⟨cost,hp⟩ := countedPrefix_of_iterN_pending observed
    exact ⟨cost,hp,room o cost turns hp before condition⟩
  · intro observations o cost turns hp before condition
    obtain ⟨other,otherPrefix,input⟩ := observations turns before o hp.iterN_eq condition
    have same := otherPrefix.cost_unique hp
    rw [same] at input
    exact input

theorem LoopCert.correct_horizon_of_observation_room {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial : Machine}
    (horizon : Nat) (repr : StateRepr L b frame F σ base initial)
    (cap : b + frameNeedProg body ≤ frame)
    (observations : ∀ (turns : Nat), turns < horizon → ∀ (o : Solidity.Out C σ.H Γ),
      TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) turns ⟨σ,List.prefix_refl _⟩=.inl o →
      c.evalT o.st=.ok true → ∃ cost, CountedLoopPrefix c body σ o cost turns ∧
        AllocationInput b frame (cost+allocationCostProg body o.st) σ base initial) :
    CountedHorizonRelation L b frame F c body σ base initial horizon
      (TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) horizon ⟨σ,List.prefix_refl _⟩)
      (loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) horizon initial) := by
  exact cert.correct_finite_horizon horizon repr cap (finiteLoopRoom_iff_observations.mpr observations)

end Solidity.Evm.Memory
