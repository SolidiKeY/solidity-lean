import Solidity.Evm.MemoryLoopHorizonCost

/-! Exact accumulated allocation cost is monotone along actual counted source
prefixes. Extending a pending execution preserves the old cost as a lower bound.
Growth need not be strict: nonallocating turns can leave cost unchanged. These
facts supply no capacity bound, allocation provenance or termination theorem. -/
namespace Solidity.Evm.Memory
variable {C : Contract} {Γ Δ : Ctx}

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

end Solidity.Evm.Memory
