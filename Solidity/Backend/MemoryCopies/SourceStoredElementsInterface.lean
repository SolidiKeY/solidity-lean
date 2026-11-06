import Solidity.Backend.MemoryCopies.SourceStoredReferences

/-! Homogeneous element traversal in the existing Source stored-value family.
The count indexes the real loadElems result; no evaluator or admission selector is added. -/
namespace Solidity.Backend.MemoryCopies

structure SourceStoredElements {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (start : Nat) (type : Source.STy) (count : Nat) where
  horizon : Nat
  objects : Nat
  horizon_positive : 0 < horizon
  execution : ∀ (input : Source.EMState E Γ), AllocationExtension before input → ∀ slack : Nat,
    ∃ (values : Fin count → Source.Data E.layout type) (after : Source.EMState E Γ),
      (Source.loadElems (E := E) (Γ := Γ) frame (horizon + slack) type path start count).run input =
        (.ok values,after) ∧ AllocationExtension input after ∧ after.2.heap.next = input.2.heap.next + objects

def SourceStoredDynamicArray {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} {element : Source.STy} {count : Nat}
    (elements : SourceStoredElements frame path before 0 element count) : Prop :=
  ∃ value : SourceStoredValue frame path before (.array .memory element none),
    value.horizon = elements.horizon + 2 ∧ value.objects = elements.objects + 1

def SourceStoredFixedArray {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} {element : Source.STy} {count : Nat}
    (elements : SourceStoredElements frame path before 0 element count) : Prop :=
  ∃ value : SourceStoredValue frame path before (.array .memory element (some count)),
    value.horizon = elements.horizon + 2 ∧ value.objects = elements.objects + 1
end Solidity.Backend.MemoryCopies
