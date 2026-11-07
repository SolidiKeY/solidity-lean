import Solidity.Backend.PrimitivePackets.Constants.Source
import Solidity.Evm.MemoryCompile

/-! Public selection of the existing integer literal. Width is enforced by
Source bounds; signedness chooses the existing target primitive carrier. -/
namespace Solidity.Backend.PrimitivePackets.Constants
open Evm Evm.Memory Solidity.Lowering.V07

abbrev value {C : Contract} {Γ : Ctx} (t : Source.IntTy) (z : Int)
    (h : t.lo ≤ z ∧ z ≤ t.hi) : Val C Γ (integerPrim t) :=
  IntegerConstants.value t z h

def selected {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) :
    CompiledVal offset F (value (C:=C) t z h) :=
  ⟨Evm.compileVal offset (value t z h), .core _ rfl⟩

theorem public_selection {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) :
    Memory.compileVal offset F (value (C:=C) t z h) = some (selected offset F t z h) := by
  rfl

theorem selected_push {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) :
    (selected (C:=C) offset F t z h).code = [.push (.val (sword z))] := by
  rfl

end Solidity.Backend.PrimitivePackets.Constants
