import Solidity.Evm.MemoryLoopFiniteHorizon

/-! A finite capacity certificate can be restricted to any smaller requested
horizon. Consumers retain the published counted-prefix relation, actual source
and target iterators, allocator provenance and exact cost. No infinite room or
termination premise is introduced, and the existing theorem statements remain
unchanged. -/
namespace Solidity.Evm.Memory
variable {C : Contract} {Γ Δ : Ctx}

theorem FiniteLoopRoom.restrict {b frame : Nat} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {horizon limit : Nat}
    (room : FiniteLoopRoom b frame c body σ base m limit) (within : horizon ≤ limit) :
    FiniteLoopRoom b frame c body σ base m horizon := by
  intro o cost turns reached before condition
  exact room o cost turns reached (Nat.lt_of_lt_of_le before within) condition

theorem LoopCert.correct_horizons_le {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (limit : Nat) (repr : StateRepr L b frame F σ base m)
    (cap : b + frameNeedProg body ≤ frame)
    (room : FiniteLoopRoom b frame c body σ base m limit) :
    ∀ horizon, horizon ≤ limit → CountedHorizonRelation L b frame F c body σ base m horizon
      (TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) horizon ⟨σ,List.prefix_refl _⟩)
      (loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) horizon m) := by
  intro horizon within
  exact cert.correct_finite_horizon horizon repr cap (room.restrict within)

end Solidity.Evm.Memory
