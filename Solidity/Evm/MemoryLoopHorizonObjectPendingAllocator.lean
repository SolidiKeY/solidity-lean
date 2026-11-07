import Solidity.Evm.MemoryLoopHorizonObjectFinite

/-! Actual pending target observations expose the complete-object source prefix
and physical representation. Positive accumulated construction cost also yields
the genuine initial and exactly grown complete allocator witnesses from finite
room. Zero cost supplies no allocator witness. No legacy allocator is promoted,
and pending execution is not classified as completion or divergence. -/
namespace Solidity.Evm.Memory.Construction
variable {C : Contract} {Γ Δ : Ctx}

theorem CountedHorizonRelation.pending_state {L b frame : Nat} {F : Frag Γ} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {initial reached : Machine} {turns : Nat}
    {source : Solidity.Out C σ.H Γ ⊕ TRes (Solidity.Out C σ.H Γ)}
    (relation : CountedHorizonRelation L b frame F c body σ base initial turns source (.inl reached)) :
    ∃ (o : Solidity.Out C σ.H Γ) (nextBase : Nat → Fin W) (cost : Nat),
      source=.inl o ∧ CountedLoopPrefix c body σ o cost turns ∧
      Objects.StateRepr L b frame F o.st nextBase reached ∧ reached.stack=initial.stack ∧
      BaseExtends σ.H base nextBase ∧ Objects.GrowsAllocator b frame cost σ base initial o.st nextBase reached := by
  cases relation with
  | more hp repr stack bases grows => exact ⟨_,_,_,rfl,hp,repr,stack,bases,grows⟩

theorem LoopCert.target_pending_prefix {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial reached : Machine}
    (n : Nat) (repr : Objects.StateRepr L b frame F σ base initial)
    (cap : b + frameNeedProg body ≤ frame) (room : FiniteLoopRoom b frame c body σ base initial n)
    (pending : loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n initial=.inl reached) :
    ∃ (o : Solidity.Out C σ.H Γ) (nextBase : Nat → Fin W) (cost : Nat),
      TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n ⟨σ,List.prefix_refl _⟩=.inl o ∧
      CountedLoopPrefix c body σ o cost n ∧ Objects.StateRepr L b frame F o.st nextBase reached ∧
      reached.stack=initial.stack ∧ BaseExtends σ.H base nextBase ∧
      Objects.GrowsAllocator b frame cost σ base initial o.st nextBase reached := by
  have relation := cert.correct_finite_horizon n repr cap room
  rw [pending] at relation
  exact relation.pending_state

theorem LoopCert.pending_allocator {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial reached : Machine}
    (n : Nat) (repr : Objects.StateRepr L b frame F σ base initial)
    (cap : b + frameNeedProg body ≤ frame) (room : FiniteLoopRoom b frame c body σ base initial n)
    (pending : loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n initial=.inl reached) :
    ∃ (o : Solidity.Out C σ.H Γ) (nextBase : Nat → Fin W) (cost : Nat),
      TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n ⟨σ,List.prefix_refl _⟩=.inl o ∧
      CountedLoopPrefix c body σ o cost n ∧ Objects.StateRepr L b frame F o.st nextBase reached ∧
      reached.stack=initial.stack ∧ BaseExtends σ.H base nextBase ∧
      Objects.GrowsAllocator b frame cost σ base initial o.st nextBase reached ∧
      (0 < cost → 0 < b ∧ ∃ (cursor : Fin W) (space : cursor.val+cost < W),
        Objects.AllocatorRepr σ.heap base frame cursor initial ∧
        Objects.AllocatorRepr o.st.heap nextBase frame ⟨cursor.val+cost,space⟩ reached) := by
  obtain ⟨o,nextBase,cost,observed,hp,current,stack,bases,grows⟩ :=
    cert.target_pending_prefix n repr cap room pending
  refine ⟨o,nextBase,cost,observed,hp,current,stack,bases,grows,?_⟩
  intro positive
  rcases room.prefix_input hp (Nat.le_refl n) with zero | ⟨enabled,cursor,initialAllocator,space⟩
  · omega
  · exact ⟨enabled,cursor,space,initialAllocator,grows cursor enabled initialAllocator space⟩

end Solidity.Evm.Memory.Construction
