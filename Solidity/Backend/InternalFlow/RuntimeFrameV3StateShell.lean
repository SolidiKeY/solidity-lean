import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarTurn

/-! Equality of existing State record fields outside memory and locals, for
allocation-only internal execution. This does not assert external/world-call
or physical byte-journal correspondence. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.StateShell

def Same {C : Contract} {Γ Δ : Ctx} (σ : State C Γ) (τ : State C Δ) : Prop :=
 σ.storage=τ.storage ∧ σ.net=τ.net ∧ σ.selfBalance=τ.selfBalance ∧ σ.tx=τ.tx

theorem refl {C : Contract} {Γ : Ctx} (σ : State C Γ) : Same σ σ := ⟨rfl,rfl,rfl,rfl⟩
theorem symm {C : Contract} {Γ Δ : Ctx} {σ : State C Γ} {τ : State C Δ}
 (same : Same σ τ) : Same τ σ := ⟨same.1.symm,same.2.1.symm,same.2.2.1.symm,same.2.2.2.symm⟩
theorem trans {C : Contract} {Γ Δ Θ : Ctx} {σ : State C Γ} {τ : State C Δ} {ρ : State C Θ}
 (first : Same σ τ) (second : Same τ ρ) : Same σ ρ :=
 ⟨first.1.trans second.1,first.2.1.trans second.2.1,first.2.2.1.trans second.2.2.1,first.2.2.2.trans second.2.2.2⟩

theorem state_eq {C : Contract} {Γ : Ctx} (σ τ : State C Γ)
 (typing : σ.H=τ.H) (heap : HEq σ.heap τ.heap) (env : HEq σ.env τ.env) (same : Same σ τ) : σ=τ := by
 cases σ
 cases τ
 cases typing
 cases heap
 cases env
 obtain ⟨rfl,rfl,rfl,rfl⟩ := same
 rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.StateShell

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.StateShell.refl' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.StateShell.refl

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.StateShell.symm' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.StateShell.symm

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.StateShell.trans' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.StateShell.trans

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.StateShell.state_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.StateShell.state_eq
