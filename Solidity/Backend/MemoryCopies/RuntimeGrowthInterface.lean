import Solidity.Backend.MemoryCopies.RuntimeRebind

/-! Connect successful existing emitted runtime defaults to the existing
compiler allocator-growth relation. Checked room stays an explicit input. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def RuntimeGrowthExecution {C : Contract} {Γ Δ : Ctx} (L b frame cost : Nat)
    (frag : Frag Δ) (before : State C Γ) (after : State C Δ)
    (base : Nat → Fin W) (machine : Machine) (code : List Instr) : Prop :=
  ∃ base' target, run code machine = .ok target 0 ∧
    Objects.StateRepr L b frame frag after base' target ∧
    Objects.GrowsAllocator b frame cost before base machine after base' target ∧
    BaseExtends before.H base base' ∧ target.stack = machine.stack

structure AllocatorGrowthCertificate : Prop where
  unique : ∀ {H : HTy} {heap : Heap H} {base : Nat → Fin W} {frame : Nat}
    {machine : Machine} {first second : Fin W},
    Objects.AllocatorRepr heap base frame first machine →
    Objects.AllocatorRepr heap base frame second machine → first = second
  reached : ∀ {C : Contract} {Γ Δ : Ctx} {b frame cost : Nat}
    {before : State C Γ} {after : State C Δ} {base base' : Nat → Fin W}
    {machine target : Machine} {cursor : Fin W},
    Objects.AllocatorRepr before.heap base frame cursor machine →
    ∀ fits : cursor.val + cost < W,
    Objects.AllocatorRepr after.heap base' frame ⟨cursor.val + cost,fits⟩ target →
    Objects.GrowsAllocator b frame cost before base machine after base' target
end Solidity.Backend.MemoryCopies
