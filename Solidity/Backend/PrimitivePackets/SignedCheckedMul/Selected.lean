import Solidity.Evm.MemoryCompile

/-! The existing public compiler selects this family. The operand loads and
original signed checked-multiplication guard (`sTail .mul`, solc's
`checked_mul_t_int256`: the `x < 0 ∧ y = -2^255` test, then the `SDIV`
round trip) are retained; no requested CompiledVal is an input. -/
namespace Solidity.Backend.PrimitivePackets.SignedCheckedMul
open Evm Evm.Memory

def value {C : Contract} {Γ : Ctx} (a b : Idx Γ (.val .int)) : Val C Γ .int :=
  .binop .mul rfl rfl (.simple (.local a)) (.simple (.local b))

def selected {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (a b : Idx Γ (.val .int)) : CompiledVal offset F (value (C:=C) a b) :=
  ⟨binaryCode .int .mul (Evm.compileVal (C:=C) offset (.simple (.local a)))
      (Evm.compileVal (C:=C) offset (.simple (.local b))),
    .binary .mul rfl rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩

theorem public_selection {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (a b : Idx Γ (.val .int)) :
    Memory.compileVal offset F (value (C:=C) a b) = some (selected offset F a b) := by
  first | rfl | decide | omega | simp only [value,selected,Memory.compileVal]

theorem original_guard {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (a b : Idx Γ (.val .int)) :
    (selected (C:=C) offset F a b).code =
      Evm.compileVal (C:=C) offset (.simple (.local a)) ++
      Evm.compileVal (C:=C) offset (.simple (.local b)) ++
      ([.dup 2,.dup 2,.mul,.push w[0],.dup 4,.slt,.push (.val wH),.dup 4,.eq,.and,.iszero] ++
       assertTop ++ [.dup 3,.dup 2,.sdiv,.dup 3,.eq,.dup 4,.iszero,.or] ++
       assertTop ++ [.swap 2,.pop,.pop]) := by rfl
/-- The selected guard is exactly `sTail .mul`, the code `Evm.smul_tail` runs. -/
theorem guard_is_sTail {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (a b : Idx Γ (.val .int)) :
    (selected (C:=C) offset F a b).code =
      Evm.compileVal (C:=C) offset (.simple (.local a)) ++
      Evm.compileVal (C:=C) offset (.simple (.local b)) ++ sTail .mul := by rfl
end Solidity.Backend.PrimitivePackets.SignedCheckedMul
