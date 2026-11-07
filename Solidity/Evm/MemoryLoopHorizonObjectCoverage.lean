import Solidity.Evm.MemoryLoopHorizonObjectPrefix

/-! Reverse coverage for the complete-object construction-cost prefix. An actual
pending source iterator constructs its counted successful execution and exact
construction cost, including continuation from a reached prefix. This reuses
the existing source iterator, not legacy allocator costs or a presumed trace.
No target-loop or Source adequacy follows from source coverage alone. -/
namespace Solidity.Evm.Memory.Construction
variable {C : Contract} {Γ Δ : Ctx}

theorem CountedLoopPrefix.extend_pending {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} :
    ∀ n {o : Solidity.Out C σ.H Γ} {cost turns : Nat},
      CountedLoopPrefix c body σ o cost turns →
      ∀ {last : Solidity.Out C σ.H Γ},
      TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n o = .inl last →
      ∃ finalCost, CountedLoopPrefix c body σ last finalCost (turns + n)
  | 0, _, _, _, hp, _, h => by cases h; exact ⟨_, hp⟩
  | n + 1, o, _, _, hp, _, h => by
    simp only [TLoop.iterN, TLoop.step] at h
    cases hc : c.evalT o.st with
    | error error => rw [hc] at h; cases h
    | ok value =>
      cases value with
      | false => rw [hc] at h; cases h
      | true =>
        rw [hc] at h
        cases hs : body.run o.st with
        | error error =>
          simp only [horizonBody, hs, Except.map] at h
          cases h
        | ok next =>
          simp only [horizonBody, hs, Except.map] at h
          obtain ⟨finalCost, hp'⟩ := CountedLoopPrefix.extend_pending n (.next hp hc hs) h
          exact ⟨finalCost, by simpa only [Nat.succ_add, Nat.add_succ] using hp'⟩

theorem countedPrefix_of_iterN_pending {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {n : Nat} {o : Solidity.Out C σ.H Γ}
    (h : TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n
      ⟨σ, List.prefix_refl _⟩ = .inl o) :
    ∃ cost, CountedLoopPrefix c body σ o cost n := by
  simpa only [Nat.zero_add] using CountedLoopPrefix.extend_pending n .start h

end Solidity.Evm.Memory.Construction
