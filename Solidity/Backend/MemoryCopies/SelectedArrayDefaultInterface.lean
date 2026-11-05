import Solidity.Backend.MemoryCopies.RuntimeArrayInterface

/-! Runtime reference arrays over any child selected by the existing default compiler.
Fixed dimensions wrap an existing reference type; no code selector is added. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def fixedDefaultType (root : RefTy) : List Nat → RefTy
  | [] => root
  | count :: rest => .fixed (.ref (fixedDefaultType root rest)) count

def selectedArrayCost (root : RefTy) (dimensions : List Nat) (size : Fin W) : Nat :=
  size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref (fixedDefaultType root dimensions))

/-- An extension of the existing DefaultBuilder proof family, carrying actual
production selection and an inhabited fitting input for the whole parent.
It does not require a fitting input for an unused child of an empty parent. -/
structure SelectedArrayDefault (root : RefTy) (dimensions : List Nat)
    (memory : (Ty.ref (fixedDefaultType root dimensions)).mapFree = true) (size : Fin W) where
  child : Objects.DefaultBuilder (fixedDefaultType root dimensions) memory
    (ReferenceDefaults.defaultCells (.ref (fixedDefaultType root dimensions)))
  selected : ReferenceDefaults.compileDefault (fixedDefaultType root dimensions) memory = some child
  feasible : V2.AllocatorWitness (selectedArrayCost root dimensions size)
end Solidity.Backend.MemoryCopies
