import Solidity.Evm.MemoryLoopHorizonObjectCoverage

/-! Determinism and monotonicity of actual complete-object construction cost.
At a fixed successful-turn count, reached state and accumulated construction
cost are unique; extension retains the old cost as a lower bound. Growth may
be zero. These facts supply no allocator capacity, physical provenance or
termination argument and do not equate construction and legacy costs. -/
namespace Solidity.Evm.Memory.Construction
variable {C : Contract} {Γ Δ : Ctx}

theorem CountedLoopPrefix.state_unique {c : Val C Γ .bool} {body : Prog C Γ Δ} {σ : State C Γ}
    {first second : Solidity.Out C σ.H Γ} {cost₁ cost₂ turns : Nat}
    (left : CountedLoopPrefix c body σ first cost₁ turns)
    (right : CountedLoopPrefix c body σ second cost₂ turns) : first=second := by
  exact Sum.inl.inj (left.iterN_eq.symm.trans right.iterN_eq)

theorem CountedLoopPrefix.cost_unique {c : Val C Γ .bool} {body : Prog C Γ Δ} {σ : State C Γ}
    {first second : Solidity.Out C σ.H Γ} {cost₁ cost₂ turns : Nat}
    (left : CountedLoopPrefix c body σ first cost₁ turns)
    (right : CountedLoopPrefix c body σ second cost₂ turns) : cost₁=cost₂ := by
  induction left generalizing second cost₂ with
  | start => cases right; rfl
  | next hp condition step ih =>
    cases right with
    | next other otherCondition otherStep =>
      have same := hp.state_unique other
      cases same
      rw [ih other]

theorem countedPrefix_of_iterN_pending_unique {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {n : Nat} {o : Solidity.Out C σ.H Γ}
    (observed : TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n
      ⟨σ,List.prefix_refl _⟩=.inl o) :
    ∃ cost, CountedLoopPrefix c body σ o cost n ∧
      ∀ other, CountedLoopPrefix c body σ o other n → other=cost := by
  obtain ⟨cost,hp⟩ := countedPrefix_of_iterN_pending observed
  exact ⟨cost,hp,fun other otherPrefix => otherPrefix.cost_unique hp⟩


theorem CountedLoopPrefix.cost_le {c : Val C Γ .bool} {body : Prog C Γ Δ} {σ : State C Γ}
    {first second : Solidity.Out C σ.H Γ} {cost₁ cost₂ earlier later : Nat}
    (left : CountedLoopPrefix c body σ first cost₁ earlier)
    (right : CountedLoopPrefix c body σ second cost₂ later) (within : earlier ≤ later) : cost₁ ≤ cost₂ := by
  induction right generalizing first cost₁ earlier with
  | start =>
    have zero : earlier=0 := by omega
    subst earlier
    cases left
    exact Nat.le_refl 0
  | @next o cost turns next hp condition step ih =>
    by_cases before : earlier ≤ turns
    · have prior := ih left before
      omega
    · have same : earlier=turns+1 := by omega
      subst earlier
      exact Nat.le_of_eq (left.cost_unique (.next hp condition step))

theorem CountedLoopPrefix.extend_pending_mono {c : Val C Γ .bool} {body : Prog C Γ Δ} {σ : State C Γ}
    {o last : Solidity.Out C σ.H Γ} {cost turns : Nat}
    (hp : CountedLoopPrefix c body σ o cost turns) (n : Nat)
    (observed : TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n o=.inl last) :
    ∃ finalCost, CountedLoopPrefix c body σ last finalCost (turns+n) ∧ cost ≤ finalCost := by
  obtain ⟨finalCost,extended⟩ := hp.extend_pending n observed
  exact ⟨finalCost,extended,hp.cost_le extended (by omega)⟩

end Solidity.Evm.Memory.Construction
