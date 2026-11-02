import Solidity.Backend.InternalFlow.PublishedDirectCalls

/-! One actual prefix endpoint supports multiple typed continuations. Capacity
is transported from the initial state; no midpoint or target run is assumed. -/
namespace Solidity.Backend.InternalFlow.SharedPrefixCapacity
open Evm Evm.Memory
variable {C : Contract}

theorem fork {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} (before : Calls.Program b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m)
    (room : b + before.need ≤ frame)
    (o : Solidity.Out C σ.H Δ) (executed : P.run σ = .ok o)
    (left right : Nat)
    (capacity : AllocationInput b frame (before.cost σ + max left right) σ base m) :
    ∃ reached addresses,
      Evm.run before.code m = .ok reached 0 ∧
      StateRepr L b frame before.frag o.st addresses reached ∧
      reached.stack = m.stack ∧ BaseExtends σ.H base addresses ∧
      GrowsAllocator b frame (before.cost σ) σ base m o.st addresses reached ∧
      AllocationInput b frame left o.st addresses reached ∧
      AllocationInput b frame right o.st addresses reached := by
  obtain ⟨reached,addresses,ht,hr,hk,he,hg⟩ :=
    PublishedDirectCalls.program_endpoint before repr room
      (capacity.of_le (Nat.le_add_right _ _)) o executed
  have both : AllocationInput b frame (max left right) o.st addresses reached :=
    hg.nextInput capacity
  exact ⟨reached,addresses,ht,hr,hk,he,hg,
    both.of_le (Nat.le_max_left _ _),both.of_le (Nat.le_max_right _ _)⟩
end Solidity.Backend.InternalFlow.SharedPrefixCapacity
