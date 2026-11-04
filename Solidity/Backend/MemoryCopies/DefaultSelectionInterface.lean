import Solidity.Backend.MemoryCopies.SelectedArrayDefaults
import Solidity.Evm.MemoryObjectConstructionCompile

/-! Selection from the existing statement compiler, not a new compiler branch.
Availability describes the existing child compiler; capacity is a separate input. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

structure SelectedDefaultDeclaration {C : Contract} {Γ : Ctx} (b : Nat) (frag : Frag Γ)
    (root : RefTy) (name : Var) (defaultable : (Ty.ref root).defaultOkS = true)
    (memory : (Ty.ref root).mapFree = true) where
  compiled : Construction.CompiledStmt (C := C) b frag (.declMem root name none defaultable memory)
  selected : Construction.compileStmt (C := C) b frag (.declMem root name none defaultable memory) = some compiled

structure DefaultSelectionCertificate : Prop where
  supported : ∀ {C : Contract} {Γ : Ctx} (b : Nat) (frag : Frag Γ) (root : RefTy) (name : Var)
    (defaultable : (Ty.ref root).defaultOkS = true) (memory : (Ty.ref root).mapFree = true),
    0 < b → (ReferenceDefaults.compileDefault root memory).isSome = true →
    (Construction.compileStmt (C := C) b frag (.declMem root name none defaultable memory)).isSome = true
end Solidity.Backend.MemoryCopies
