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

theorem two_reference {R S Q : RefTy} (reference : HRef [R,S] Q) :
    (Q = R ∧ HEq reference (⟨0,rfl⟩ : HRef [R,S] R)) ∨
      (Q = S ∧ HEq reference (⟨1,rfl⟩ : HRef [R,S] S)) := by
  rcases reference with ⟨index,selected⟩
  cases index with
  | zero => cases selected; exact .inl ⟨rfl,HEq.rfl⟩
  | succ index => cases index with
    | zero => cases selected; exact .inr ⟨rfl,HEq.rfl⟩
    | succ index => cases selected

theorem two_array_heap_repr {R S : RefTy} {E F : Ty} {heap : Heap [R,S]}
    {base : Nat → Fin W} {frame : Nat} {machine : Machine}
    (shapeR : ArrTy R E) (shapeS : ArrTy S F)
    (aboveR : frame ≤ (base 0).val) (aboveS : frame ≤ (base 1).val)
    (apart : (base 0).val + Objects.cells heap (⟨0,rfl⟩ : HRef [R,S] R) ≤ (base 1).val ∨
      (base 1).val + Objects.cells heap (⟨1,rfl⟩ : HRef [R,S] S) ≤ (base 0).val)
    (representedR : Objects.ArrayRepr heap (⟨0,rfl⟩ : HRef [R,S] R) shapeR base machine)
    (representedS : Objects.ArrayRepr heap (⟨1,rfl⟩ : HRef [R,S] S) shapeS base machine) :
    Objects.HeapRepr heap base frame machine := by
  have noStruct {name : Name} (reference : HRef [R,S] (.struct name)) : False := by
    rcases two_reference reference with ⟨same,_⟩ | ⟨same,_⟩
    · exact shapeR.ne_struct name same.symm
    · exact shapeS.ne_struct name same.symm
  refine ⟨⟨?_,?_,?_⟩,?_,?_,RefFieldsRepr.withoutStructs heap base machine noStruct⟩
  · intro Q reference
    rcases two_reference reference with ⟨rfl,equal⟩ | ⟨rfl,equal⟩
    · cases equal; exact aboveR
    · cases equal; exact aboveS
  · intro Q reference
    rcases two_reference reference with ⟨rfl,equal⟩ | ⟨rfl,equal⟩
    · cases equal; exact representedR.space
    · cases equal; exact representedS.space
  · intro Q T left right different
    rcases two_reference left with ⟨rfl,leftEq⟩ | ⟨rfl,leftEq⟩ <;> cases leftEq
      <;> rcases two_reference right with ⟨rfl,rightEq⟩ | ⟨rfl,rightEq⟩ <;> cases rightEq
    · exact (different rfl).elim
    · exact apart
    · exact apart.elim Or.inr Or.inl
    · exact (different rfl).elim
  · intro A G array reference
    rcases two_reference reference with ⟨rfl,equal⟩ | ⟨rfl,equal⟩
    · cases equal; cases shapeR <;> cases array <;> exact representedR
    · cases equal; cases shapeS <;> cases array <;> exact representedS
  · intro name reference
    exact (noStruct reference).elim

end Solidity.Backend.MemoryCopies
