import Solidity.Backend.PrimitivePackets.UnsignedDiv.Data
import Solidity.Evm.MemoryCompile

/-! Concrete certificates are internal proof data. The selection laws below
establish that the EXISTING public compiler actually returns them; callers do
not supply a compiled value, desired run or poststate. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedDiv

variable {C : Contract} {Γ : Solidity.Ctx}

def selectedDiv (b : Nat) (F : Evm.Frag (modelContext Γ)) :
    Evm.Memory.CompiledVal b F (modelDiv C Γ) :=
  ⟨Evm.Memory.binaryCode .uint .div
      (Evm.compileVal b (.simple (.local (.here : Idx (modelContext Γ) (.val .uint)))))
      (Evm.compileVal b (.simple (.local (.there .here)))),
    .binary .div rfl rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩

def selectedMod (b : Nat) (F : Evm.Frag (modelContext Γ)) :
    Evm.Memory.CompiledVal b F (modelMod C Γ) :=
  ⟨Evm.Memory.binaryCode .uint .mod
      (Evm.compileVal b (.simple (.local (.here : Idx (modelContext Γ) (.val .uint)))))
      (Evm.compileVal b (.simple (.local (.there .here)))),
    .binary .mod rfl rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩

theorem select_div (b : Nat) (F : Evm.Frag (modelContext Γ)) :
    Evm.Memory.compileVal b F (modelDiv C Γ) = some (selectedDiv b F) := by
  rfl

theorem select_mod (b : Nat) (F : Evm.Frag (modelContext Γ)) :
    Evm.Memory.compileVal b F (modelMod C Γ) = some (selectedMod b F) := by
  rfl

/-- Both genuine local reads and the zero-checking arithmetic suffix are
retained in the selected code. -/
theorem div_code (b : Nat) (F : Evm.Frag (modelContext Γ)) :
    (selectedDiv (C := C) b F).code =
      [.mload (Evm.cellOf b (.here : Idx (modelContext Γ) (.val .uint))),
       .mload (Evm.cellOf b ((.there .here) : Idx (modelContext Γ) (.val .uint)))] ++
        Evm.binTail .uint .div := by
  rfl

theorem mod_code (b : Nat) (F : Evm.Frag (modelContext Γ)) :
    (selectedMod (C := C) b F).code =
      [.mload (Evm.cellOf b (.here : Idx (modelContext Γ) (.val .uint))),
       .mload (Evm.cellOf b ((.there .here) : Idx (modelContext Γ) (.val .uint)))] ++
        Evm.binTail .uint .mod := by
  rfl

end Solidity.Backend.PrimitivePackets.UnsignedDiv
