import Solidity.Backend.Passes.Boundary

/-!
# Arbitrary saved stack tails at compilation boundaries

No input representation reads the operand stack. The allocator and base map
remain correlated with the same source heap; changing a tail cannot weaken
those obligations. The success result applies to each arbitrary tail, rather
than only to an empty initial stack.
-/
namespace Solidity.Backend.Passes

open Solidity.Evm
open Solidity.Evm.Compiler

variable {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ}

private theorem allocation_stack {cost : Nat} {σ : State C Γ}
    {base : Nat → Fin W} {m : Machine}
    (h : Memory.AllocationInput b frame cost σ base m) (tail : List Word) :
    Memory.AllocationInput b frame cost σ base {m with stack := tail} := by
  rcases h with h | ⟨hb, cursor, ha, hs⟩
  · exact .inl h
  · exact .inr ⟨hb, cursor, ha.stack tail, hs⟩

private theorem object_allocation_stack {cost : Nat} {σ : State C Γ}
    {base : Nat → Fin W} {m : Machine}
    (h : Memory.Objects.AllocationInput b frame cost σ base m) (tail : List Word) :
    Memory.Objects.AllocationInput b frame cost σ base {m with stack := tail} := by
  rcases h with h | ⟨hb, cursor, ha, hs⟩
  · exact .inl h
  · exact .inr ⟨hb, cursor, ha.stack tail, hs⟩

private theorem object_state_stack {σ : State C Γ}
    {base : Nat → Fin W} {m : Machine}
    (h : Memory.Objects.StateRepr L b frame F σ base m) (tail : List Word) :
    Memory.Objects.StateRepr L b frame F σ base {m with stack := tail} :=
  ⟨h.core.stack tail, h.heap.stack tail, h.pointers, h.locals⟩

/-- All eight constructor-specific input relations admit an arbitrary saved
stack, retaining their original frame, allocator and typed-value premises. -/
theorem compilation_input_stack (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m) (tail : List Word) :
    result.Input L frame base σ {m with stack := tail} := by
  cases result with
  | core out cert => exact ⟨hi.1.stack tail, hi.2⟩
  | memory out =>
    exact ⟨hi.1.stack tail, hi.2.1, allocation_stack hi.2.2 tail⟩
  | referenceArrays out =>
    exact ⟨hi.state.stack tail, hi.arrays.stack tail⟩
  | objects out =>
    exact ⟨object_state_stack hi.1 tail, hi.2⟩
  | construction out =>
    exact ⟨object_state_stack hi.1 tail, hi.2.1, object_allocation_stack hi.2.2 tail⟩
  | memoryLoops out =>
    exact ⟨hi.1.stack tail, hi.2.1, fun amount hd => allocation_stack (hi.2.2 amount hd) tail⟩
  | memoryLoopScopes out =>
    exact ⟨hi.1.stack tail, hi.2.1, fun amount hd => allocation_stack (hi.2.2 amount hd) tail⟩
  | memoryCalls out pushFree =>
    exact ⟨hi.1.stack tail, hi.2.1, allocation_stack hi.2.2 tail⟩

/-- Replacing a tail changes neither admissibility nor resource requirements. -/
theorem compilation_input_stack_iff (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine} (tail : List Word) :
    result.Input L frame base σ {m with stack := tail} ↔
      result.Input L frame base σ m :=
  ⟨fun h => compilation_input_stack result h m.stack,
    fun h => compilation_input_stack result h tail⟩

/-- Every successful payment-free source run compiles successfully with every
saved tail and returns that exact tail. The output keeps the complete Rep. -/
theorem compilation_success_tail (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m) (hpay : Evm.Prog.pays P = false)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o) (tail : List Word) :
    ∃ m', run result.code {m with stack := tail} = .ok m' 0 ∧
      m'.stack = tail ∧ result.Rep (L + Evm.Prog.pushes P) frame base
        σ {m with stack := tail} o.st m' :=
  compilation_success result (compilation_input_stack result hi tail) hpay hs

end Solidity.Backend.Passes
