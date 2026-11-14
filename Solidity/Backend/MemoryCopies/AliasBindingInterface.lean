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

theorem singleton_reference {R Q : RefTy} (reference : HRef [R] Q) :
    Q = R ∧ HEq reference (⟨0,rfl⟩ : HRef [R] R) := by
  rcases reference with ⟨index,selected⟩
  cases index with
  | zero => cases selected; exact ⟨rfl,HEq.rfl⟩
  | succ index => cases selected

theorem singleton_array_heap_repr {R : RefTy} {E : Ty} {heap : Heap [R]}
    {base : Nat → Fin W} {frame : Nat} {machine : Machine} (shape : ArrTy R E)
    (above : frame ≤ (base 0).val)
    (represented : Objects.ArrayRepr heap (⟨0,rfl⟩ : HRef [R] R) shape base machine) :
    Objects.HeapRepr heap base frame machine := by
  have noStruct {name : Name} (reference : HRef [R] (.struct name)) : False :=
    shape.ne_struct name (singleton_reference reference).1.symm
  refine ⟨⟨?_,?_,?_⟩,?_,?_,RefFieldsRepr.withoutStructs heap base machine noStruct⟩
  · intro Q reference
    obtain ⟨rfl,equal⟩ := singleton_reference reference
    cases equal
    exact above
  · intro Q reference
    obtain ⟨rfl,equal⟩ := singleton_reference reference
    cases equal
    exact represented.space
  · intro Q S left right different
    obtain ⟨rfl,leftEq⟩ := singleton_reference left
    obtain ⟨rfl,rightEq⟩ := singleton_reference right
    cases leftEq
    cases rightEq
    exact (different rfl).elim
  · intro A F array reference
    obtain ⟨rfl,equal⟩ := singleton_reference reference
    cases equal
    cases shape <;> cases array <;> exact represented
  · intro name reference
    exact (noStruct reference).elim


theorem memory_pair_state_repr {C : Contract} {R Q : RefTy} {L b frame : Nat}
    {F : Frag [.mem R,.mem Q]} {state : State C [.mem R,.mem Q]}
    {base : Nat → Fin W} {machine : Machine}
    (core : Sim C L b F state machine) (heap : Objects.HeapRepr state.heap base frame machine)
    (head : HRef state.H R) (tail : HRef state.H Q)
    (environment : state.env = (some head,(some tail,())))
    (headPointer : machine.mem (b + 1) = .val (base head.id))
    (tailPointer : machine.mem b = .val (base tail.id)) (locals : b + 2 ≤ frame) :
    Objects.StateRepr L b frame F state base machine := by
  refine ⟨core,heap,?_,locals⟩
  intro S index
  cases index with
  | here => exact ⟨head,environment.symm ▸ rfl,headPointer⟩
  | there index => cases index with
    | here => exact ⟨tail,environment.symm ▸ rfl,tailPointer⟩
    | there index => nomatch index

end Solidity.Backend.MemoryCopies
