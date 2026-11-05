import Solidity.Evm.MemoryLoopFiniteHorizon

/-! Actual pending target observations expose the corresponding counted source
prefix and its complete represented physical-state facts. This consumes the
published relation and finite transport; no target/source agreement is assumed
as an output field, and a pending prefix is not classified as completion or
divergence. Exact accumulated allocation cost and base growth are retained. -/
namespace Solidity.Evm.Memory
variable {C : Contract} {Γ Δ : Ctx}

theorem CountedHorizonRelation.pending_state {L b frame : Nat} {F : Frag Γ} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {initial reached : Machine} {turns : Nat}
    {source : Solidity.Out C σ.H Γ ⊕ TRes (Solidity.Out C σ.H Γ)}
    (relation : CountedHorizonRelation L b frame F c body σ base initial turns source (.inl reached)) :
    ∃ (o : Solidity.Out C σ.H Γ) (nextBase : Nat → Fin W) (cost : Nat),
      source=.inl o ∧ CountedLoopPrefix c body σ o cost turns ∧
      StateRepr L b frame F o.st nextBase reached ∧ reached.stack=initial.stack ∧
      BaseExtends σ.H base nextBase ∧ GrowsAllocator b frame cost σ base initial o.st nextBase reached := by
  cases relation with
  | more hp repr stack bases grows => exact ⟨_,_,_,rfl,hp,repr,stack,bases,grows⟩

theorem LoopCert.target_pending_prefix {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial reached : Machine}
    (n : Nat) (repr : StateRepr L b frame F σ base initial)
    (cap : b + frameNeedProg body ≤ frame) (room : FiniteLoopRoom b frame c body σ base initial n)
    (pending : loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n initial=.inl reached) :
    ∃ (o : Solidity.Out C σ.H Γ) (nextBase : Nat → Fin W) (cost : Nat),
      TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n ⟨σ,List.prefix_refl _⟩=.inl o ∧
      CountedLoopPrefix c body σ o cost n ∧ StateRepr L b frame F o.st nextBase reached ∧
      reached.stack=initial.stack ∧ BaseExtends σ.H base nextBase ∧
      GrowsAllocator b frame cost σ base initial o.st nextBase reached := by
  have relation := cert.correct_finite_horizon n repr cap room
  rw [pending] at relation
  exact relation.pending_state

end Solidity.Evm.Memory
