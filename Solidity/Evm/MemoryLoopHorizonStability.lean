import Solidity.Evm.MemoryLoopFiniteHorizon

/-! Once the actual source iterator has a terminal observation, no successful
counted prefix can occur at a later turn. The finite capacity already needed
through that observation therefore suffices at every requested horizon. This
is conditional on actual completion (including a terminal revert), not an
unconditional termination or unbounded-allocation claim. -/
namespace Solidity.Evm.Memory
variable {C : Contract} {Γ Δ : Ctx}

theorem FiniteLoopRoom.after_completion {b frame : Nat} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {initial : Machine} {n : Nat}
    {result : TRes (Solidity.Out C σ.H Γ)}
    (room : FiniteLoopRoom b frame c body σ base initial n)
    (finished : TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n
      ⟨σ,List.prefix_refl _⟩=.inr result) (horizon : Nat) :
    FiniteLoopRoom b frame c body σ base initial horizon := by
  intro o cost turns hp before condition
  by_cases earlier : turns<n
  · exact room o cost turns hp earlier condition
  · have terminal := TLoop.iterN_done_le (by omega : n ≤ turns) finished
    rw [hp.iterN_eq] at terminal
    cases terminal

theorem LoopCert.correct_horizons_after_completion {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial : Machine}
    (n : Nat) (repr : StateRepr L b frame F σ base initial)
    (cap : b + frameNeedProg body ≤ frame) (room : FiniteLoopRoom b frame c body σ base initial n)
    {result : TRes (Solidity.Out C σ.H Γ)}
    (finished : TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n
      ⟨σ,List.prefix_refl _⟩=.inr result) (horizon : Nat) :
    CountedHorizonRelation L b frame F c body σ base initial horizon
      (TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) horizon ⟨σ,List.prefix_refl _⟩)
      (loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) horizon initial) := by
  exact cert.correct_finite_horizon horizon repr cap (room.after_completion finished horizon)

end Solidity.Evm.Memory
