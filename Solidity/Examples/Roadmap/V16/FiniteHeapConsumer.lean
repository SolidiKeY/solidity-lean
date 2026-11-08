import Solidity.Examples.Roadmap.V16.ConstructionConsumer
/-! Consumers of three actual finite-heap compiler arms. Branch-specific Input
and Rep remain unchanged; no Source admission or byte-EVM claim. -/
namespace Solidity.Roadmap.V16
open Solidity.Evm

theorem finite_heap_result {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemory = true ∨ compiled.isReferenceArray = true ∨ compiled.isObject = true)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (input : compiled.Input L frame base σ m) :
    (∃ o m', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ compiled.Rep L frame base σ m o.st m') ∨
    (P.run σ = .error .revert ∧ run compiled.code m = .revert) := by
  cases compiled with
  | memoryCopy _ => rcases path with h | h | h <;> cases h
  | fixedMemory _ => rcases path with h | h | h <;> cases h
  | copyConstruction _ => rcases path with h | h | h <;> cases h
  | core _ _ => rcases path with h | h | h <;> cases h
  | construction _ => rcases path with h | h | h <;> cases h
  | memoryLoops _ => rcases path with h | h | h <;> cases h
  | memoryLoopScopes _ => rcases path with h | h | h <;> cases h
  | memoryCalls _ _ => rcases path with h | h | h <;> cases h
  | memory out =>
    rcases out.cert.correct input.1 input.2.1 input.2.2 with
      ⟨o,m',base',hs,ht,repr,stack,extension,grows⟩ | h
    · exact .inl ⟨o,m',hs,ht,stack,base',repr,extension,grows⟩
    · exact .inr h
  | referenceArrays out =>
    rcases out.cert.correct input with ⟨o,m',hs,ht,repr,stack⟩ | h
    · exact .inl ⟨o,m',hs,ht,stack,repr⟩
    · exact .inr h
  | objects out =>
    rcases out.cert.correct input.1 input.2 with ⟨o,m',hs,ht,repr,stack,keeps⟩ | h
    · exact .inl ⟨o,m',hs,ht,stack,repr,keeps⟩
    · exact .inr h

theorem finite_heap_not_exhausted {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemory = true ∨ compiled.isReferenceArray = true ∨ compiled.isObject = true)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (input : compiled.Input L frame base σ m) : P.run σ ≠ .error .exhausted := by
  intro h
  rcases finite_heap_result compiled path input with ⟨o,_,hs,_⟩ | ⟨hs,_⟩
  all_goals rw [h] at hs; cases hs

theorem finite_heap_diamond {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemory = true ∨ compiled.isReferenceArray = true ∨ compiled.isObject = true)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {φ : Spec C Δ}
    (input : compiled.Input L frame base σ m) (diamond : Spec.sat σ (.diamond P φ)) :
    ∃ o m', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ compiled.Rep L frame base σ m o.st m' ∧ Spec.sat o.st φ := by
  obtain ⟨o,source,post⟩ := spec_diamond_success diamond (finite_heap_not_exhausted compiled path input)
  rcases finite_heap_result compiled path input with ⟨u,m',hs,ht,stack,repr⟩ | ⟨hs,_⟩
  · have eq : u = o := Except.ok.inj (hs.symm.trans source)
    subst u
    exact ⟨o,m',source,ht,stack,repr,post⟩
  · rw [source] at hs; cases hs

theorem finite_heap_box {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemory = true ∨ compiled.isReferenceArray = true ∨ compiled.isObject = true)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {φ : Spec C Δ}
    (input : compiled.Input L frame base σ m) (box : Spec.sat σ (.box P φ)) :
    (∃ o m', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ compiled.Rep L frame base σ m o.st m' ∧ Spec.sat o.st φ) ∨
    (P.run σ = .error .revert ∧ run compiled.code m = .revert) := by
  rcases finite_heap_result compiled path input with ⟨o,m',hs,ht,stack,repr⟩ | h
  · exact .inl ⟨o,m',hs,ht,stack,repr,spec_box_post box hs⟩
  · exact .inr h

/-- Exact error consequence of the finite certificates, including the payload. -/
theorem finite_heap_failure {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemory = true ∨ compiled.isReferenceArray = true ∨ compiled.isObject = true)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    {e : THalt} (input : compiled.Input L frame base σ m) (source : P.run σ = .error e) :
    e = .revert ∧ run compiled.code m = .revert := by
  rcases finite_heap_result compiled path input with ⟨_,_,hs,_⟩ | ⟨hs,ht⟩
  · rw [source] at hs; cases hs
  · rw [source] at hs
    exact ⟨Except.error.inj hs,ht⟩

/-- The actual diamond is equivalent to a complete represented success witness. -/
theorem finite_heap_diamond_iff {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemory = true ∨ compiled.isReferenceArray = true ∨ compiled.isObject = true)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {φ : Spec C Δ}
    (input : compiled.Input L frame base σ m) :
    Spec.sat σ (.diamond P φ) ↔ ∃ o m', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ compiled.Rep L frame base σ m o.st m' ∧ Spec.sat o.st φ := by
  constructor
  · exact finite_heap_diamond compiled path input
  · rintro ⟨o,_,hs,_,_,_,post⟩
    simpa only [Spec.sat,hs] using post

/-- Box permits exact empty revert and otherwise retains every success observation. -/
theorem finite_heap_box_iff {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemory = true ∨ compiled.isReferenceArray = true ∨ compiled.isObject = true)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {φ : Spec C Δ}
    (input : compiled.Input L frame base σ m) :
    Spec.sat σ (.box P φ) ↔ (∃ o m', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ compiled.Rep L frame base σ m o.st m' ∧ Spec.sat o.st φ) ∨
      (P.run σ = .error .revert ∧ run compiled.code m = .revert) := by
  constructor
  · exact finite_heap_box compiled path input
  · rintro (⟨o,_,hs,_,_,_,post⟩ | ⟨hs,_⟩)
    · simpa only [Spec.sat,hs] using post
    · simp only [Spec.sat,hs,ne_eq,reduceCtorEq,not_false_eq_true]

/-- Primitive finite allocation retains its actual source-computed cost. -/
theorem finite_memory_cost {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemory = true) (σ : State C Γ) :
    compiled.allocationCost σ = Memory.allocationCostProg P σ := by
  cases compiled with
  | memoryCopy _ => rcases path with h | h | h <;> cases h
  | fixedMemory _ => rcases path with h | h | h <;> cases h
  | copyConstruction _ => rcases path with h | h | h <;> cases h
  | core _ _ => cases path
  | memory _ => rfl
  | referenceArrays _ => cases path
  | objects _ => cases path
  | construction _ => cases path
  | memoryLoops _ => cases path
  | memoryLoopScopes _ => cases path
  | memoryCalls _ _ => cases path

/-- Preserve the complete growing primitive-memory relation without unfolding a computed certificate. -/
theorem finite_memory_rep_iff {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemory = true) {L frame : Nat} {σ : State C Γ} {τ : State C Δ}
    {base : Nat → Fin W} {m m' : Machine} :
    compiled.Rep L frame base σ m τ m' ↔ ∃ base',
      Memory.StateRepr L b frame compiled.frag τ base' m' ∧ Memory.BaseExtends σ.H base base' ∧
      Memory.GrowsAllocator b frame (compiled.allocationCost σ) σ base m τ base' m' := by
  cases compiled with
  | memoryCopy _ => rcases path with h | h | h <;> cases h
  | fixedMemory _ => rcases path with h | h | h <;> cases h
  | copyConstruction _ => rcases path with h | h | h <;> cases h
  | core _ _ => cases path
  | memory _ => rfl
  | referenceArrays _ => cases path
  | objects _ => cases path
  | construction _ => cases path
  | memoryLoops _ => cases path
  | memoryLoopScopes _ => cases path
  | memoryCalls _ _ => cases path
end Solidity.Roadmap.V16
