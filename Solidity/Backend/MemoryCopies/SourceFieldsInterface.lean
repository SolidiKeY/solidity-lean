import Solidity.Backend.MemoryCopies.SourceConstructionInterface

/-! Heterogeneous fields over the existing Source default traversal. -/
namespace Solidity.Backend.MemoryCopies

/-- Actual successful zeroVal execution for a primitive value or a proved
reference constructor. It adds no interpreter, compiler or admission selector. -/
structure SourceValueConstruction (E : Source.Env) (τ : Source.STy) where
  horizon : Nat
  objects : Nat
  horizon_positive : 0 < horizon
  execution : ∀ {Γ : Source.RCtx} (before : Source.EMState E Γ) (slack : Nat),
    ∃ (value : Source.Val E.layout τ) (after : Source.EMState E Γ),
      (Source.zeroVal (E := E) (Γ := Γ) (horizon + slack) τ).run before = (.ok value,after) ∧
      AllocationExtension before after ∧ after.2.heap.next = before.2.heap.next + objects

/-- Actual zeroFields execution and object count at the exact existing field
list. Struct consumers must supply the actual environment's layout field list. -/
structure SourceFieldsConstruction (E : Source.Env) (types : List Source.STy) where
  horizon : Nat
  objects : Nat
  horizon_positive : 0 < horizon
  execution : ∀ {Γ : Source.RCtx} (before : Source.EMState E Γ) (slack : Nat),
    ∃ (data : Source.DataList E.layout types) (after : Source.EMState E Γ),
      (Source.zeroFields (E := E) (Γ := Γ) (horizon + slack) types).run before = (.ok data,after) ∧
      AllocationExtension before after ∧ after.2.heap.next = before.2.heap.next + objects

end Solidity.Backend.MemoryCopies
