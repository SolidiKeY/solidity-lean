import Solidity.Evm.MemoryLoopHorizonObjectFinite

/-! Observable outcomes of complete-object finite transport: pending and revert
agreement, and no target fault under the actual strong representation, owner
certificates, frame and finite-room premises. An observed finite revert also
determines the existing unbounded runs. No rollback, unconditional termination,
infinite capacity or pending-as-divergence claim is made. -/
namespace Solidity.Evm.Memory.Construction
variable {C : Contract} {Γ Δ : Ctx}

theorem CountedHorizonRelation.pending_iff {L b frame : Nat} {F : Frag Γ} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {turns : Nat}
    {source : Solidity.Out C σ.H Γ ⊕ TRes (Solidity.Out C σ.H Γ)} {target : Machine ⊕ Out}
    (h : CountedHorizonRelation L b frame F c body σ base m turns source target) :
    (∃ o,source=.inl o) ↔ (∃ reached,target=.inl reached) := by
  cases h with
  | more => exact ⟨fun _ => ⟨_,rfl⟩,fun _ => ⟨_,rfl⟩⟩
  | done =>
    constructor <;> rintro ⟨_,same⟩ <;> cases same
  | revert =>
    constructor <;> rintro ⟨_,same⟩ <;> cases same

theorem CountedHorizonRelation.revert_iff {L b frame : Nat} {F : Frag Γ} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {turns : Nat}
    {source : Solidity.Out C σ.H Γ ⊕ TRes (Solidity.Out C σ.H Γ)} {target : Machine ⊕ Out}
    (h : CountedHorizonRelation L b frame F c body σ base m turns source target) :
    source=.inr (.error .revert) ↔ target=.inr .revert := by
  cases h with
  | more => constructor <;> intro same <;> cases same
  | done => constructor <;> intro same <;> cases same
  | revert => exact ⟨fun _ => rfl,fun _ => rfl⟩

theorem CountedHorizonRelation.no_fault {L b frame : Nat} {F : Frag Γ} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {turns : Nat}
    {source : Solidity.Out C σ.H Γ ⊕ TRes (Solidity.Out C σ.H Γ)} {target : Machine ⊕ Out}
    (h : CountedHorizonRelation L b frame F c body σ base m turns source target) : target≠.inr .fault := by
  cases h <;> intro same <;> cases same

theorem LoopCert.horizon_no_fault {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (n : Nat) (repr : Objects.StateRepr L b frame F σ base m)
    (cap : b + frameNeedProg body ≤ frame) (room : FiniteLoopRoom b frame c body σ base m n) :
    loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n m≠.inr .fault := by
  exact (cert.correct_finite_horizon n repr cap room).no_fault


theorem LoopCert.finite_revert_iff {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial : Machine}
    (n : Nat) (repr : Objects.StateRepr L b frame F σ base initial)
    (cap : b + frameNeedProg body ≤ frame) (room : FiniteLoopRoom b frame c body σ base initial n) :
    TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n ⟨σ,List.prefix_refl _⟩=.inr (.error .revert) ↔ loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n initial=.inr .revert := by
  exact (cert.correct_finite_horizon n repr cap room).revert_iff

theorem LoopCert.reverted_runs {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial : Machine}
    (n : Nat) (repr : Objects.StateRepr L b frame F σ base initial)
    (cap : b + frameNeedProg body ≤ frame) (room : FiniteLoopRoom b frame c body σ base initial n)
    (reverted : loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n initial=.inr .revert) :
    TLoop.run (horizonBody body) (fun o => c.evalT o.st) ⟨σ,List.prefix_refl _⟩=.error .revert ∧
    loopRun (fun m => exec cond 0 m) (fun m => exec code 0 m) initial=.revert := by
  have source := (cert.finite_revert_iff n repr cap room).mpr reverted
  exact ⟨TLoop.run_of_iterN source,loopRun_of_iterN reverted⟩

end Solidity.Evm.Memory.Construction
