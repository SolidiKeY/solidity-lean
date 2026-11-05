import Solidity.Backend.MemoryCopies.InterfaceV2Laws

/-! Selection obligations over the existing production default compiler.
Dimensions describe a family of intrinsic reference types, not a new AST or
admission classifier. Source graph/layout refinement remains separate. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

/-- Fixed-array dimensions around an empty dynamic-array default. The base
may itself have reference elements; an empty default allocates no elements. -/
def nestedArrayType (element : Ty) : List Nat → RefTy
  | [] => .array element
  | n :: rest => .fixed (.ref (nestedArrayType element rest)) n

/-- A production-selected builder with an actual fitting allocator input.
This is a success certificate; runtime size failures are separate obligations. -/
structure SelectedNestedDefault (element : Ty) (dimensions : List Nat)
    (memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true) where
  certified : V2.DefaultCertificate (nestedArrayType element dimensions) memory
    (ReferenceDefaults.defaultCells (.ref (nestedArrayType element dimensions)))
  selected : ReferenceDefaults.compileDefault (nestedArrayType element dimensions) memory =
    some certified.builder

end Solidity.Backend.MemoryCopies
