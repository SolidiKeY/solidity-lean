import Solidity.Evm.MemoryCompile
import Solidity.Lowering.V07.UnsignedMultiplication

/-! Public compiler selection for unchecked multiplication of two runtime locals.
The width cleaner is the existing mulValue; no new syntax or compiler clause. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedMul
open Evm Evm.Memory Solidity.Lowering.V07
open Solidity.Lowering.V07.UnsignedMultiplication

def expression {C : Contract} {Γ : Ctx} (bits : Nat)
    (a b : Idx Γ (.val .uint)) : Val C Γ .uint :=
  mulValue bits (.simple (.local a)) (.simple (.local b))

theorem selectable {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (bits : Nat) (a b : Idx Γ (.val .uint)) :
    (Memory.compileVal (C := C) offset F (expression bits a b)).isSome = true := by
  by_cases h : bits < 256
  · dsimp only [expression, mulValue]
    rw [dif_pos h]
    rfl
  · dsimp only [expression, mulValue]
    rw [dif_neg h]
    rfl

def selected {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (bits : Nat) (a b : Idx Γ (.val .uint)) :
    CompiledVal offset F (expression (C := C) bits a b) :=
  (Memory.compileVal offset F (expression bits a b)).get (selectable offset F bits a b)

theorem selection {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (bits : Nat) (a b : Idx Γ (.val .uint)) :
    Memory.compileVal (C := C) offset F (expression bits a b) =
      some (selected offset F bits a b) :=
  (Option.some_get _).symm

end Solidity.Backend.PrimitivePackets.UnsignedMul
