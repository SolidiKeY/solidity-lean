import Solidity.Backend.Passes.CoreBoundary

/-! Finite physical links between actual branch-indexed compiler certificates.
The complete MappedOutput is consumed at its selected map. No core/legacy
relation is upgraded to stronger heap ownership. -/
namespace Solidity.Backend.Passes
open Evm Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}
  {base : Nat → Fin W} {σ : State C Γ} {m : Machine}

theorem referenceArrays_memory_link (left : Memory.ReferenceArrays.CompiledProg b F P)
    (right : Memory.CompiledProg b left.frag Q)
    (capacity : b + Memory.frameNeedProg Q ≤ frame)
    (nonallocating : Memory.hasAllocation Q = false) :
    MappedBoundaryLink (.referenceArrays left) (.memory right) L frame base σ m := by
  intro o mid selected _ _ output
  exact ⟨output.2.state, capacity, .inl (Memory.allocationCostProg_zero Q nonallocating o.st)⟩

theorem objects_memory_link (left : Memory.Objects.CompiledProg b F P)
    (right : Memory.CompiledProg b left.frag Q)
    (capacity : b + Memory.frameNeedProg Q ≤ frame)
    (nonallocating : Memory.hasAllocation Q = false) :
    MappedBoundaryLink (.objects left) (.memory right) L frame base σ m := by
  intro o mid selected _ _ output
  exact ⟨output.2.1.legacy, capacity, .inl (Memory.allocationCostProg_zero Q nonallocating o.st)⟩

theorem construction_memory_link (left : Memory.Construction.CompiledProg b F P)
    (right : Memory.CompiledProg b left.frag Q)
    (capacity : b + Memory.frameNeedProg Q ≤ frame)
    (nonallocating : Memory.hasAllocation Q = false) :
    MappedBoundaryLink (.construction left) (.memory right) L frame base σ m := by
  intro o mid selected _ _ output
  exact ⟨output.1.legacy, capacity, .inl (Memory.allocationCostProg_zero Q nonallocating o.st)⟩

theorem objects_referenceArrays_link (left : Memory.Objects.CompiledProg b F P)
    (right : Memory.ReferenceArrays.CompiledProg b left.frag Q) :
    MappedBoundaryLink (.objects left) (.referenceArrays right) L frame base σ m := by
  intro o mid selected _ _ output
  exact output.2.1.reference

theorem construction_referenceArrays_link (left : Memory.Construction.CompiledProg b F P)
    (right : Memory.ReferenceArrays.CompiledProg b left.frag Q) :
    MappedBoundaryLink (.construction left) (.referenceArrays right) L frame base σ m := by
  intro o mid selected _ _ output
  exact output.1.reference

theorem objects_objects_link (left : Memory.Objects.CompiledProg b F P)
    (right : Memory.Objects.CompiledProg b left.frag Q)
    (capacity : b + Memory.frameNeedProg Q ≤ frame) :
    MappedBoundaryLink (.objects left) (.objects right) L frame base σ m := by
  intro o mid selected _ _ output
  exact ⟨output.2.1, capacity⟩

theorem construction_objects_link (left : Memory.Construction.CompiledProg b F P)
    (right : Memory.Objects.CompiledProg b left.frag Q)
    (capacity : b + Memory.frameNeedProg Q ≤ frame) :
    MappedBoundaryLink (.construction left) (.objects right) L frame base σ m := by
  intro o mid selected _ _ output
  exact ⟨output.1, capacity⟩

/-- Allocation is transported using the REAL object's reached allocator and
sum budget. A zero-cost suffix does not stand in for an allocating one. -/
theorem construction_budgeted_link (left : Memory.Construction.CompiledProg b F P)
    (right : Memory.Construction.CompiledProg b left.frag Q)
    (capacity : b + Memory.frameNeedProg Q ≤ frame)
    (budget : ∀ o : Solidity.Out C σ.H Δ, P.run σ = .ok o →
      Memory.Objects.AllocationInput b frame
        (Memory.Construction.allocationCostProg P σ + Memory.Construction.allocationCostProg Q o.st)
        σ base m) :
    MappedBoundaryLink (.construction left) (.construction right) L frame base σ m := by
  intro o mid selected hs _ output
  exact ⟨output.1, capacity, output.2.2.nextInput (budget o hs)⟩

end Solidity.Backend.Passes
