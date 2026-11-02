import Solidity.Backend.InternalFlow.LocalStoreFlow
/-! Retain the real reached allocator input and both actual finite frames.
This refines the existing program/statement consumer without a simulation oracle. -/
namespace Solidity.Backend.InternalFlow.LocalStoreFlow
open Evm Evm.Memory
variable {C : Contract}
theorem program_statement_frames {b L frame : Nat} {Γ Δ Ξ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} {s : Stmt C Δ Ξ}
    (before : Calls.Program b F P) (after : Calls.Statement b before.frag s)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m)
    (roomBefore : b + before.need ≤ frame) (roomAfter : b + after.need ≤ frame)
    (middle : Solidity.Out C σ.H Δ) (out : Solidity.Out C middle.st.H Ξ)
    (capacity : AllocationInput b frame (before.cost σ + after.cost middle.st) σ base m)
    (hp : P.run σ = .ok middle) (hs : s.run middle.st = .ok out) :
    ∃ m₁ base₁ m₂ base₂,
      Evm.run before.code m = .ok m₁ 0 ∧ Evm.run after.code m₁ = .ok m₂ 0 ∧
      StateRepr L b frame before.frag middle.st base₁ m₁ ∧
      StateRepr L b frame after.frag out.st base₂ m₂ ∧
      m₁.stack = m.stack ∧ m₂.stack = m₁.stack ∧
      BaseExtends σ.H base base₁ ∧ BaseExtends middle.st.H base₁ base₂ ∧
      GrowsAllocator b frame (before.cost σ) σ base m middle.st base₁ m₁ ∧
      GrowsAllocator b frame (after.cost middle.st) middle.st base₁ m₁ out.st base₂ m₂ ∧
      AllocationInput b frame (after.cost middle.st) middle.st base₁ m₁ := by
  obtain ⟨m₁,base₁,ht,hr,hk,he,hg⟩ := PublishedDirectCalls.program_endpoint before repr roomBefore
    (capacity.of_le (Nat.le_add_right _ _)) middle hp
  have reachedInput := hg.nextInput capacity
  obtain ⟨m₂,base₂,ht',hr',hk',he',hg'⟩ := PublishedDirectCalls.statement_endpoint after hr roomAfter
    reachedInput out hs
  exact ⟨m₁,base₁,m₂,base₂,ht,ht',hr,hr',hk,hk',he,he',hg,hg',reachedInput⟩
end Solidity.Backend.InternalFlow.LocalStoreFlow
