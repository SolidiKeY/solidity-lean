import Solidity.Evm.MemoryCompile

/-! The existing public compiler selects this family. The operand loads and
original checked-add guard are retained; no requested CompiledVal is an input. -/
namespace Solidity.Backend.PrimitivePackets.SignedCheckedAdd
open Evm Evm.Memory

def value {C : Contract} {Γ : Ctx} (a b : Idx Γ (.val .int)) : Val C Γ .int :=
  .binop .add rfl rfl (.simple (.local a)) (.simple (.local b))

def selected {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (a b : Idx Γ (.val .int)) : CompiledVal offset F (value (C:=C) a b) :=
  ⟨binaryCode .int .add (Evm.compileVal (C:=C) offset (.simple (.local a)))
      (Evm.compileVal (C:=C) offset (.simple (.local b))),
    .binary .add rfl rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩

theorem public_selection {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (a b : Idx Γ (.val .int)) :
    Memory.compileVal offset F (value (C:=C) a b) = some (selected offset F a b) := by
  first | rfl | decide | omega | simp only [value,selected,Memory.compileVal]

theorem original_guard {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (a b : Idx Γ (.val .int)) :
    (selected (C:=C) offset F a b).code =
      Evm.compileVal (C:=C) offset (.simple (.local a)) ++
      Evm.compileVal (C:=C) offset (.simple (.local b)) ++
      (sTail .add) := by
  first | rfl | decide | omega | simp only [selected,binaryCode,binTail,uTail]
end Solidity.Backend.PrimitivePackets.SignedCheckedAdd
