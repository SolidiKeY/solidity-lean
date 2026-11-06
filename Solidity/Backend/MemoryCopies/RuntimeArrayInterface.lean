import Solidity.Backend.MemoryCopies.NestedDefaultInterface
import Solidity.Evm.MemoryReferenceDefaultSource

/-! Runtime-length construction from production-selected child defaults.
Feasibility belongs to the complete parent demand, not to an unused child. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def runtimeNestedCost (element : Ty) (dimensions : List Nat) (size : Fin W) : Nat :=
  size.val + 1 + size.val * ReferenceDefaults.defaultCells
    (.ref (nestedArrayType element dimensions))

/-- Actual production-selected child and one fitting input for the ENTIRE
runtime construction. No separate child-feasibility exclusion is introduced.
This certifies successful word-memory construction, not Source admission or
runtime allocation-failure selection. -/
structure RuntimeNestedDefault (element : Ty) (dimensions : List Nat)
    (memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true) (size : Fin W) where
  child : Objects.DefaultBuilder (nestedArrayType element dimensions) memory
    (ReferenceDefaults.defaultCells (.ref (nestedArrayType element dimensions)))
  selected : ReferenceDefaults.compileDefault (nestedArrayType element dimensions) memory = some child
  feasible : V2.AllocatorWitness (runtimeNestedCost element dimensions size)

end Solidity.Backend.MemoryCopies
