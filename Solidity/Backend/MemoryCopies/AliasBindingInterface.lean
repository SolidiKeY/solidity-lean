import Solidity.Evm.MemoryObjectStatements

/-! Alias binding uses the existing path compiler and emitted local store. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

/-- Selection is tied to the existing pointer compiler, including its existing
path support. This does not manufacture admission for a rejected path. -/
structure SelectedAlias {C : Contract} {Γ : Ctx} (b : Nat) (frag : Frag Γ)
    {R : RefTy} (path : MPath C Γ (.ref R)) where
  pointer : Objects.CompiledPtr b frag path
  selected : Objects.compilePtr b frag path = some pointer

/-- Exact success or bounds refusal for an actual alias rebind. Success keeps
all heap objects, caller stack and any supplied complete allocator. -/
def AliasBindingOutcome {C : Contract} {Γ : Ctx} {R : RefTy}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ)
    (base : Nat → Fin W) (machine : Machine) (path : MPath C Γ (.ref R))
    (destination : Idx Γ (.mem R)) (code : List Instr) : Prop :=
  (∃ reference target,
    path.mvalT state = .ok reference ∧
    TRun.rebindMem destination (.alias path) state =
      .ok ⟨state.setLocal destination (some reference), List.prefix_refl _⟩ ∧
    run code machine = .ok target 0 ∧
    Objects.StateRepr L b frame frag (state.setLocal destination (some reference)) base target ∧
    target.stack = machine.stack ∧
    Objects.KeepsAllocator b frame state base machine (state.setLocal destination (some reference)) target) ∨
  (path.mvalT state = .error .revert ∧
    TRun.rebindMem destination (.alias path) state = .error .revert ∧ run code machine = .revert)

end Solidity.Backend.MemoryCopies
