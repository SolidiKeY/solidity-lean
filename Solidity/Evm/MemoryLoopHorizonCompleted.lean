import Solidity.Evm.MemoryLoopFiniteHorizon

/-! Actual completed target horizons expose a stopped counted source prefix,
its represented physical state and exact accumulated allocation cost. Completed
finite observations also determine the existing unbounded source/target runs.
This needs only the published finite capacity certificate plus an actual target
completion; it does not assert termination or infinite allocator room. -/
namespace Solidity.Evm.Memory
variable {C : Contract} {Γ Δ : Ctx}

theorem CountedHorizonRelation.completed_state {L b frame : Nat} {F : Frag Γ} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {initial reached : Machine} {turns : Nat}
    {source : Solidity.Out C σ.H Γ ⊕ TRes (Solidity.Out C σ.H Γ)}
    (relation : CountedHorizonRelation L b frame F c body σ base initial turns source (.inr (.ok reached 0))) :
    ∃ (o : Solidity.Out C σ.H Γ) (nextBase : Nat → Fin W) (cost count : Nat),
      source=.inr (.ok o) ∧ CountedLoopPrefix c body σ o cost count ∧ count < turns ∧
      c.evalT o.st=.ok false ∧ StateRepr L b frame F o.st nextBase reached ∧
      reached.stack=initial.stack ∧ BaseExtends σ.H base nextBase ∧
      GrowsAllocator b frame cost σ base initial o.st nextBase reached := by
  cases relation with
  | done hp earlier stopped repr stack bases grows =>
    exact ⟨_,_,_,_,rfl,hp,earlier,stopped,repr,stack,bases,grows⟩

theorem LoopCert.target_completed_prefix {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial reached : Machine}
    (n : Nat) (repr : StateRepr L b frame F σ base initial)
    (cap : b + frameNeedProg body ≤ frame) (room : FiniteLoopRoom b frame c body σ base initial n)
    (completed : loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n initial=.inr (.ok reached 0)) :
    ∃ (o : Solidity.Out C σ.H Γ) (nextBase : Nat → Fin W) (cost count : Nat),
      TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n ⟨σ,List.prefix_refl _⟩=.inr (.ok o) ∧ CountedLoopPrefix c body σ o cost count ∧ count < n ∧
      c.evalT o.st=.ok false ∧ StateRepr L b frame F o.st nextBase reached ∧
      reached.stack=initial.stack ∧ BaseExtends σ.H base nextBase ∧
      GrowsAllocator b frame cost σ base initial o.st nextBase reached := by
  have relation := cert.correct_finite_horizon n repr cap room
  rw [completed] at relation
  exact relation.completed_state

theorem LoopCert.completed_runs {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial reached : Machine}
    (n : Nat) (repr : StateRepr L b frame F σ base initial)
    (cap : b + frameNeedProg body ≤ frame) (room : FiniteLoopRoom b frame c body σ base initial n)
    (completed : loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n initial=.inr (.ok reached 0)) :
    ∃ (o : Solidity.Out C σ.H Γ),
      TLoop.run (horizonBody body) (fun o => c.evalT o.st) ⟨σ,List.prefix_refl _⟩=.ok o ∧
      loopRun (fun m => exec cond 0 m) (fun m => exec code 0 m) initial=.ok reached 0 := by
  obtain ⟨o,_,_,_,observed,_⟩ := cert.target_completed_prefix n repr cap room completed
  exact ⟨o,TLoop.run_of_iterN observed,loopRun_of_iterN completed⟩

end Solidity.Evm.Memory
