import Solidity.Evm.MemoryCompile

/-! The existing public compiler selects this family. The operand loads and
original checked-subtraction guard are retained; no requested CompiledVal is an input. -/
namespace Solidity.Backend.PrimitivePackets.SignedCheckedSub
open Evm Evm.Memory

def value {C : Contract} {Γ : Ctx} (a b : Idx Γ (.val .int)) : Val C Γ .int :=
  .binop .sub rfl rfl (.simple (.local a)) (.simple (.local b))

def selected {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (a b : Idx Γ (.val .int)) : CompiledVal offset F (value (C:=C) a b) :=
  ⟨binaryCode .int .sub (Evm.compileVal (C:=C) offset (.simple (.local a)))
      (Evm.compileVal (C:=C) offset (.simple (.local b))),
    .binary .sub rfl rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩

theorem public_selection {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (a b : Idx Γ (.val .int)) :
    Memory.compileVal offset F (value (C:=C) a b) = some (selected offset F a b) := by
  first | rfl | decide | omega | simp only [value,selected,Memory.compileVal]

theorem original_guard {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (a b : Idx Γ (.val .int)) :
    (selected (C:=C) offset F a b).code =
      Evm.compileVal (C:=C) offset (.simple (.local a)) ++
      Evm.compileVal (C:=C) offset (.simple (.local b)) ++
      ([.dup 1,.dup 3,.sub,.dup 1,.dup 4,.slt,.push w[0],.dup 4,.slt,.eq] ++
       assertTop ++ [.swap 2,.pop,.pop]) := by rfl
end Solidity.Backend.PrimitivePackets.SignedCheckedSub
