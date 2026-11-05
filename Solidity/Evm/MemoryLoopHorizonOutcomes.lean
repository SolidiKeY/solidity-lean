import Solidity.Evm.MemoryLoopFiniteHorizon

/-! Observable consequences of the published counted finite-horizon transport.
Pending observations agree, reverts agree, and target fault is excluded only
under the actual certificate, representation, frame and finite-capacity premises.
No pending horizon is classified as divergence or completed execution. -/
namespace Solidity.Evm.Memory
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
    (n : Nat) (repr : StateRepr L b frame F σ base m)
    (cap : b + frameNeedProg body ≤ frame) (room : FiniteLoopRoom b frame c body σ base m n) :
    loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n m≠.inr .fault := by
  exact (cert.correct_finite_horizon n repr cap room).no_fault

end Solidity.Evm.Memory
