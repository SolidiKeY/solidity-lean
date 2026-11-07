import Solidity.Evm.MemoryLoopHorizonPending

/-! Finite room supplies capacity for each reached counted prefix, including
its terminal boundary count. At positive accumulated cost, an actual pending
target therefore exposes the owner's initial and exactly grown struct
allocator witnesses. Zero cost remains vacuous and does not fabricate an
allocator. Existing capacity, representation and execution premises are retained. -/
namespace Solidity.Evm.Memory
variable {C : Contract} {Γ Δ : Ctx}

theorem FiniteLoopRoom.prefix_input {b frame : Nat} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {initial : Machine} {horizon : Nat}
    (room : FiniteLoopRoom b frame c body σ base initial horizon)
    {o : Solidity.Out C σ.H Γ} {cost turns : Nat}
    (hp : CountedLoopPrefix c body σ o cost turns) (within : turns ≤ horizon) :
    AllocationInput b frame cost σ base initial := by
  cases hp with
  | start => exact .inl rfl
  | next previous condition step => exact room _ _ _ previous (by omega) condition

theorem LoopCert.pending_allocator {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial reached : Machine}
    (n : Nat) (repr : StateRepr L b frame F σ base initial)
    (cap : b + frameNeedProg body ≤ frame) (room : FiniteLoopRoom b frame c body σ base initial n)
    (pending : loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n initial=.inl reached) :
    ∃ (o : Solidity.Out C σ.H Γ) (nextBase : Nat → Fin W) (cost : Nat),
      TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n ⟨σ,List.prefix_refl _⟩=.inl o ∧
      CountedLoopPrefix c body σ o cost n ∧ StateRepr L b frame F o.st nextBase reached ∧
      reached.stack=initial.stack ∧ BaseExtends σ.H base nextBase ∧
      GrowsAllocator b frame cost σ base initial o.st nextBase reached ∧
      (0 < cost → 0 < b ∧ ∃ (cursor : Fin W) (space : cursor.val+cost < W),
        StructAllocatorRepr σ.heap base frame cursor initial ∧
        StructAllocatorRepr o.st.heap nextBase frame ⟨cursor.val+cost,space⟩ reached) := by
  obtain ⟨o,nextBase,cost,observed,hp,current,stack,bases,grows⟩ :=
    cert.target_pending_prefix n repr cap room pending
  refine ⟨o,nextBase,cost,observed,hp,current,stack,bases,grows,?_⟩
  intro positive
  rcases room.prefix_input hp (Nat.le_refl n) with zero | ⟨enabled,cursor,initialAllocator,space⟩
  · omega
  · exact ⟨enabled,cursor,space,initialAllocator,grows cursor enabled initialAllocator space⟩

end Solidity.Evm.Memory
