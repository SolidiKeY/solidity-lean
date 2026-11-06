import Solidity.Backend.MemoryCopies.SourceNestedBytesInterface

/-! Actual heterogeneous Source storage traversal, stable under child allocations.
These are proof certificates over existing operations, not another evaluator. -/
namespace Solidity.Backend.MemoryCopies

/-- A proved loadElem family at the actual path. AllocationExtension permits
only the intermediate memory growth of sibling copies, preserving storage. -/
structure SourceStoredValue {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (type : Source.STy) where
  horizon : Nat
  objects : Nat
  horizon_positive : 0 < horizon
  execution : ∀ (input : Source.EMState E Γ), AllocationExtension before input → ∀ slack : Nat,
    ∃ (value : Source.Val E.layout type) (after : Source.EMState E Γ),
      (Source.loadElem (E := E) (Γ := Γ) frame (horizon + slack) type path).run input = (.ok value,after) ∧
      AllocationExtension input after ∧ after.2.heap.next = input.2.heap.next + objects

/-- Existing loadFields traversal at an exact heterogeneous field list and
starting field index, with actual reached state and exact object count. -/
structure SourceStoredFields {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (start : Nat) (types : List Source.STy) where
  horizon : Nat
  objects : Nat
  horizon_positive : 0 < horizon
  execution : ∀ (input : Source.EMState E Γ), AllocationExtension before input → ∀ slack : Nat,
    ∃ (data : Source.DataList E.layout types) (after : Source.EMState E Γ),
      (Source.loadFields (E := E) (Γ := Γ) frame (horizon + slack) types path start).run input = (.ok data,after) ∧
      AllocationExtension input after ∧ after.2.heap.next = input.2.heap.next + objects

end Solidity.Backend.MemoryCopies
