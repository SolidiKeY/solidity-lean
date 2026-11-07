import Solidity.Evm.MemoryLoopFiniteHorizon

/-! Counted source prefixes have a deterministic reached state and exact
accumulated allocation cost at a fixed turn count. Actual pending observations
therefore produce a unique cost witness, using the published execution-to-prefix
construction. This does not bound that cost or supply allocator capacity. -/
namespace Solidity.Evm.Memory
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

end Solidity.Evm.Memory
