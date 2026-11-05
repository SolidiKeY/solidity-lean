import Solidity.Evm.MemoryLoopHorizonOutcomes

/-! A finite observed revert determines both existing loop run results under
the published finite transport premises. Source/target revert equivalence is
derived from the counted relation, not assumed. Pending horizons remain distinct;
no termination, rollback, or infinite allocation capacity is asserted. -/
namespace Solidity.Evm.Memory
variable {C : Contract} {Γ Δ : Ctx}

theorem LoopCert.finite_revert_iff {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial : Machine}
    (n : Nat) (repr : StateRepr L b frame F σ base initial)
    (cap : b + frameNeedProg body ≤ frame) (room : FiniteLoopRoom b frame c body σ base initial n) :
    TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n ⟨σ,List.prefix_refl _⟩=.inr (.error .revert) ↔ loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n initial=.inr .revert := by
  exact (cert.correct_finite_horizon n repr cap room).revert_iff

theorem LoopCert.reverted_runs {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial : Machine}
    (n : Nat) (repr : StateRepr L b frame F σ base initial)
    (cap : b + frameNeedProg body ≤ frame) (room : FiniteLoopRoom b frame c body σ base initial n)
    (reverted : loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n initial=.inr .revert) :
    TLoop.run (horizonBody body) (fun o => c.evalT o.st) ⟨σ,List.prefix_refl _⟩=.error .revert ∧
    loopRun (fun m => exec cond 0 m) (fun m => exec code 0 m) initial=.revert := by
  have source := (cert.finite_revert_iff n repr cap room).mpr reverted
  exact ⟨TLoop.run_of_iterN source,loopRun_of_iterN reverted⟩

end Solidity.Evm.Memory
