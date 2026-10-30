import Solidity.Evm.Correct
import Solidity.Evm.MemoryCompile
import Solidity.Evm.MemoryFixedCompile
import Solidity.Evm.MemoryStorageConstructionCompile
import Solidity.Evm.MemoryRefArrayCompile
import Solidity.Evm.MemoryObjectCompile
import Solidity.Evm.MemoryObjectConstructionCompile

/-!
# The checked compiler entry

One entry selects the existing core compiler when its fragment applies,
otherwise the allocating memory or published supplementary compiler routes,
then the memory-preserving fixed-copy refinement. Its result retains the corresponding fragment
certificate. The common agreement theorem preserves the stronger heap and
pointer relation on the memory path; its input states that relation and the
reserved frame bound explicitly.
-/
namespace Solidity.Evm.Compiler

variable {C : Contract}

inductive Compilation (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) where
  | core (frag : Frag Δ) (cert : inFragP F P = some frag)
  | memory (result : Memory.CompiledProg b F P)
  | referenceArrays (result : Memory.ReferenceArrays.CompiledProg b F P)
  | objects (result : Memory.Objects.CompiledProg b F P)
  | construction (result : Memory.Construction.CompiledProg b F P)
  | fixedMemory (result : Memory.Fixed.CompiledProg b F P)
  | copyConstruction (result : Memory.CopyConstruction.CompiledProg b F P)

def compile (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) :
    Option (Compilation b F P) :=
  match hc : inFragP F P with
  | some frag => some (.core frag hc)
  | none => match Memory.compileProg b F P with
    | some result => some (.memory result)
    | none => match Memory.ReferenceArrays.compileProg b F P with
      | some result => some (.referenceArrays result)
      | none => match Memory.Objects.compileProg b F P with
        | some result => some (.objects result)
        | none => match Memory.Construction.compileProg b F P with
          | some result => some (.construction result)
          | none => match Memory.Fixed.compileProg b F P with
            | some result => some (.fixedMemory result)
            | none => (Memory.CopyConstruction.compileProg b F P).map .copyConstruction

namespace Compilation

def code {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ} :
    Compilation b F P → List Instr
  | .core _ _ => Evm.compileProg b P
  | .memory result => result.code
  | .referenceArrays result => result.code
  | .objects result => result.code
  | .construction result => result.code
  | .fixedMemory result => result.code
  | .copyConstruction result => result.code

def frag {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ} :
    Compilation b F P → Frag Δ
  | .core out _ => out
  | .memory result => result.frag
  | .referenceArrays result => result.frag
  | .objects result => result.frag
  | .construction result => result.frag
  | .fixedMemory result => result.frag
  | .copyConstruction result => result.frag

def isMemory {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ} :
    Compilation b F P → Bool
  | .core _ _ => false
  | .memory _ => true
  | .referenceArrays _ | .objects _ | .construction _ | .fixedMemory _ | .copyConstruction _ => false

/-- Select the supplementary, nonallocating reference-array relation. -/
def isReferenceArray {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ} :
    Compilation b F P → Bool
  | .referenceArrays _ => true
  | .core .. | .memory .. | .objects .. | .construction .. | .fixedMemory .. | .copyConstruction .. => false

/-- Select full object ownership for the headerless fixed-array path. -/
def isObject {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ} :
    Compilation b F P → Bool
  | .objects _ => true
  | .core .. | .memory .. | .referenceArrays .. | .construction .. | .fixedMemory .. | .copyConstruction .. => false

/-- Select checked reference-array construction with a complete allocator. -/
def isConstruction {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ} :
    Compilation b F P → Bool
  | .construction _ => true
  | .core .. | .memory .. | .referenceArrays .. | .objects .. | .fixedMemory .. | .copyConstruction .. => false

def isFixedMemory {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ} :
    Compilation b F P → Bool
  | .fixedMemory _ => true
  | .core .. | .memory .. | .referenceArrays .. | .objects .. | .construction .. | .copyConstruction .. => false

def usesMemory {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ} :
    Compilation b F P → Bool
  | .core _ _ => false
  | .memory _ | .referenceArrays _ | .objects _ | .construction _ | .fixedMemory _ | .copyConstruction _ => true

/-- Select allocation/mutation composed with certified copies. -/
def isCopyConstruction {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ} :
    Compilation b F P → Bool
  | .copyConstruction _ => true
  | .core .. | .memory .. | .referenceArrays .. | .objects .. | .construction .. | .fixedMemory .. => false

def Input {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (L frame : Nat) (base : Nat → Fin W)
    (σ : State C Γ) (m : Machine) : Prop :=
  match result with
  | .core _ _ => Sim C L b F σ m ∧ L + Evm.Prog.pushes P ≤ Lmax
  | .memory out => Memory.StateRepr L b frame F σ base m ∧ b + Memory.frameNeedProg P ≤ frame ∧
      Memory.AllocationInput b frame (out.cert.cost σ) σ base m ∧ Memory.copyBoundProg P σ ≤ L
  | .referenceArrays _ => Memory.RefArrayStateRepr L b frame F σ base m
  | .objects _ => Memory.Objects.StateRepr L b frame F σ base m ∧
      b + Memory.frameNeedProg P ≤ frame
  | .construction _ => Memory.Objects.StateRepr L b frame F σ base m ∧
      b + Memory.frameNeedProg P ≤ frame ∧
      Memory.Objects.AllocationInput b frame (Memory.Construction.allocationCostProg P σ) σ base m

  | .fixedMemory _ => Memory.FixedStateRepr L b frame F σ base m ∧ Memory.copyBoundProg P σ ≤ L

  | .copyConstruction _ => Memory.Objects.StateRepr L b frame F σ base m ∧
      b + Memory.frameNeedProg P ≤ frame ∧
      Memory.Objects.AllocationInput b frame (Memory.Construction.allocationCostProg P σ) σ base m ∧
      Memory.copyBoundProg P σ ≤ L

/-- Open all memory premises, including the reached copy representation bound. -/
theorem memory_copy_input {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (hm : result.isMemory = true) (L frame : Nat)
    (base : Nat → Fin W) (σ : State C Γ) (m : Machine) :
    result.Input L frame base σ m ↔ Memory.StateRepr L b frame F σ base m ∧
      b + Memory.frameNeedProg P ≤ frame ∧
      Memory.AllocationInput b frame (Memory.allocationCostProg P σ) σ base m ∧
      Memory.copyBoundProg P σ ≤ L := by
  cases result with
  | core out cert => cases hm
  | memory out => rfl
  | referenceArrays out => cases hm
  | objects out => cases hm
  | construction out => cases hm
  | fixedMemory out => cases hm
  | copyConstruction out => cases hm

/-- The fixed route exposes its additional actual heap-payload representation. -/
theorem fixed_input {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (hf : result.isFixedMemory = true) (L frame : Nat)
    (base : Nat → Fin W) (σ : State C Γ) (m : Machine) :
    result.Input L frame base σ m ↔ Memory.FixedStateRepr L b frame F σ base m ∧
      Memory.copyBoundProg P σ ≤ L := by
  cases result with
  | core out cert => cases hf
  | memory out => cases hf
  | referenceArrays out => cases hf
  | objects out => cases hf
  | construction out => cases hf
  | fixedMemory out => rfl
  | copyConstruction out => cases hf

/-- Existing copy-free programs retain their original input premises exactly. -/
theorem memory_input {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (hm : result.isMemory = true) (L frame : Nat)
    (base : Nat → Fin W) (σ : State C Γ) (m : Machine)
    (hcopy : Memory.hasArrayCopy P = false := by decide) :
    result.Input L frame base σ m ↔ Memory.StateRepr L b frame F σ base m ∧
      b + Memory.frameNeedProg P ≤ frame ∧
      Memory.AllocationInput b frame (Memory.allocationCostProg P σ) σ base m := by
  rw [result.memory_copy_input hm]
  rw [Memory.copyBoundProg_zero P hcopy σ]
  simp only [Nat.zero_le, and_true]

/-- Open a reference-array input without unfolding the computed compiler result. -/
theorem referenceArray_input {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (hm : result.isReferenceArray = true) (L frame : Nat)
    (base : Nat → Fin W) (σ : State C Γ) (m : Machine) :
    result.Input L frame base σ m ↔ Memory.RefArrayStateRepr L b frame F σ base m := by
  cases result with
  | core out cert => cases hm
  | memory out => cases hm
  | referenceArrays out => rfl
  | objects out => cases hm
  | construction out => cases hm
  | fixedMemory out => cases hm
  | copyConstruction out => cases hm

/-- Open the full object input without unfolding the computed compiler. -/
theorem object_input {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (hm : result.isObject = true) (L frame : Nat)
    (base : Nat → Fin W) (σ : State C Γ) (m : Machine) :
    result.Input L frame base σ m ↔ Memory.Objects.StateRepr L b frame F σ base m ∧
      b + Memory.frameNeedProg P ≤ frame := by
  cases result with
  | core out cert => cases hm
  | memory out => cases hm
  | referenceArrays out => cases hm
  | objects out => rfl
  | construction out => cases hm
  | fixedMemory out => cases hm
  | copyConstruction out => cases hm

/-- Open the growing constructor premises without unfolding proof data. -/
theorem construction_input {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (hm : result.isConstruction = true) (L frame : Nat)
    (base : Nat → Fin W) (σ : State C Γ) (m : Machine) :
    result.Input L frame base σ m ↔ Memory.Objects.StateRepr L b frame F σ base m ∧
      b + Memory.frameNeedProg P ≤ frame ∧
      Memory.Objects.AllocationInput b frame (Memory.Construction.allocationCostProg P σ) σ base m := by
  cases result with
  | core out cert => cases hm
  | memory out => cases hm
  | referenceArrays out => cases hm
  | objects out => cases hm
  | construction out => rfl
  | fixedMemory out => cases hm
  | copyConstruction out => cases hm

/-- Full ownership, reached allocation capacity and reached successful copy bounds. -/
theorem copyConstruction_input {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (hm : result.isCopyConstruction = true) (L frame : Nat)
    (base : Nat → Fin W) (σ : State C Γ) (m : Machine) :
    result.Input L frame base σ m ↔ Memory.Objects.StateRepr L b frame F σ base m ∧
      b + Memory.frameNeedProg P ≤ frame ∧
      Memory.Objects.AllocationInput b frame (Memory.Construction.allocationCostProg P σ) σ base m ∧
      Memory.copyBoundProg P σ ≤ L := by
  cases result with
  | core out cert => cases hm
  | memory out => cases hm
  | referenceArrays out => cases hm
  | objects out => cases hm
  | construction out => cases hm
  | fixedMemory out => cases hm
  | copyConstruction out => rfl

def Rep {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (L frame : Nat) (base : Nat → Fin W)
    (entry : State C Γ) (initial : Machine) (σ : State C Δ) (m : Machine) : Prop :=
  match result with
  | .core out _ => Sim C L b out σ m
  | .memory out => ∃ base', Memory.StateRepr L b frame out.frag σ base' m ∧
      Memory.BaseExtends entry.H base base' ∧
      Memory.GrowsAllocator b frame (out.cert.cost entry) entry base initial σ base' m
  | .referenceArrays out => Memory.RefArrayStateRepr L b frame out.frag σ base m
  | .objects out => Memory.Objects.StateRepr L b frame out.frag σ base m ∧
      Memory.Objects.KeepsAllocator b frame entry base initial σ m
  | .construction out => ∃ base', Memory.Objects.StateRepr L b frame out.frag σ base' m ∧
      Memory.BaseExtends entry.H base base' ∧
      Memory.Objects.GrowsAllocator b frame (Memory.Construction.allocationCostProg P entry)
        entry base initial σ base' m

  | .fixedMemory out => Memory.FixedStateRepr L b frame out.frag σ base m ∧
      m.mem = initial.mem ∧ σ.H = entry.H ∧ HEq σ.heap entry.heap

  | .copyConstruction _ => ∃ base', Memory.Objects.StateRepr L b frame result.frag σ base' m ∧
      Memory.BaseExtends entry.H base base' ∧
      Memory.Objects.GrowsAllocator b frame (Memory.Construction.allocationCostProg P entry)
        entry base initial σ base' m

/-- Expose the full output relation without reducing a certified compiler value. -/
theorem object_rep {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (hm : result.isObject = true) (L frame : Nat)
    (base : Nat → Fin W) (entry : State C Γ) (initial : Machine)
    (σ : State C Δ) (m : Machine) :
    result.Rep L frame base entry initial σ m ↔
      Memory.Objects.StateRepr L b frame result.frag σ base m ∧
      Memory.Objects.KeepsAllocator b frame entry base initial σ m := by
  cases result with
  | core out cert => cases hm
  | memory out => cases hm
  | referenceArrays out => cases hm
  | objects out => rfl
  | construction out => cases hm
  | fixedMemory out => cases hm
  | copyConstruction out => cases hm


/-- Open the complete constructor output relation without unfolding the compiler. -/
theorem construction_rep {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (hm : result.isConstruction = true) (L frame : Nat)
    (base : Nat → Fin W) (entry : State C Γ) (initial : Machine)
    (σ : State C Δ) (m : Machine) :
    result.Rep L frame base entry initial σ m ↔
      ∃ base', Memory.Objects.StateRepr L b frame result.frag σ base' m ∧
        Memory.BaseExtends entry.H base base' ∧
        Memory.Objects.GrowsAllocator b frame (Memory.Construction.allocationCostProg P entry)
          entry base initial σ base' m := by
  cases result with
  | core out cert => cases hm
  | memory out => cases hm
  | referenceArrays out => cases hm
  | objects out => cases hm
  | construction out => rfl
  | fixedMemory out => cases hm
  | copyConstruction out => cases hm

/-- The compiler preserves typed states and the evaluation stack, or both
executions revert; the existing panic and payment cases retain their guards. -/
def Agrees {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (L frame : Nat) (base : Nat → Fin W)
    (σ : State C Γ) (m : Machine) : Prop :=
  (∃ o m', P.run σ = .ok o ∧ run result.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
    result.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m') ∨
  ((P.run σ = .error .revert ∨ (P.asserts = true ∧ P.run σ = .error .panic)) ∧
    run result.code m = .revert) ∨
  (Evm.Prog.pays P = true ∧ run result.code m = .revert ∧ ∃ o m',
    P.run σ = .ok o ∧ result.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m') ∨
  (P.run σ = .error .diverge ∧ (run result.code m = .fault ∨
    (Evm.Prog.pays P = true ∧ run result.code m = .revert)))

theorem correct {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (h : result.Input L frame base σ m) : result.Agrees L frame base σ m := by
  cases result with
  | core out cert => exact Evm.compile_correct cert h.1 h.2
  | memory out =>
    simp only [Agrees, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct h.1 h.2.1 h.2.2.1 h.2.2.2 with
      ⟨o, m', base', ho, hc, hm, hst, he, ha⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, base', hm, he, ha⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)

  | referenceArrays out =>
    simp only [Agrees, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct h with ⟨o, m', ho, hc, hm, hst⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, hm⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)

  | objects out =>
    simp only [Agrees, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct h.1 h.2 with ⟨o, m', ho, hc, hm, hst, ha⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, hm, ha⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)

  | construction out =>
    simp only [Agrees, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct h.1 h.2.1 h.2.2 with
      ⟨o, m', base', ho, hc, hm, hst, he, ha⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, base', hm, he, ha⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)

  | fixedMemory out =>
    simp only [Agrees, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct h.1 h.2 with
      ⟨o, m', ho, hc, hm, hst, hmem, hH, hheap⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, hm, hmem, hH, hheap⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)

  | copyConstruction out =>
    simp only [Agrees, code, Rep, out.cert.pushes_zero, Nat.add_zero, frag]
    rcases out.cert.correct h.1 h.2.1 h.2.2.1 h.2.2.2 with
      ⟨o, m', base', ho, hc, hm, hst, he, ha⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, base', hm, he, ha⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)

end Compilation
end Solidity.Evm.Compiler
