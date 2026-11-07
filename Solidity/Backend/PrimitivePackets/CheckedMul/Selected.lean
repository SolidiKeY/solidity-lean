import Solidity.Evm.MemoryCompile

/-! The existing public compiler selects this family. The operand loads and
original checked-mul guard are retained; no requested CompiledVal is an input. -/
namespace Solidity.Backend.PrimitivePackets.CheckedMul
open Evm Evm.Memory

def value {C : Contract} {Γ : Ctx} (a b : Idx Γ (.val .uint)) : Val C Γ .uint :=
  .binop .mul rfl rfl (.simple (.local a)) (.simple (.local b))

def selected {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (a b : Idx Γ (.val .uint)) : CompiledVal offset F (value (C:=C) a b) :=
  ⟨binaryCode .uint .mul (Evm.compileVal (C:=C) offset (.simple (.local a)))
      (Evm.compileVal (C:=C) offset (.simple (.local b))),
    .binary .mul rfl rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩

theorem public_selection {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (a b : Idx Γ (.val .uint)) :
    Memory.compileVal offset F (value (C:=C) a b) = some (selected offset F a b) := by
  first | rfl | decide | omega | simp only [value,selected,Memory.compileVal]

theorem original_guard {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (a b : Idx Γ (.val .uint)) :
    (selected (C:=C) offset F a b).code =
      Evm.compileVal (C:=C) offset (.simple (.local a)) ++
      Evm.compileVal (C:=C) offset (.simple (.local b)) ++
      ([.dup 2,.dup 2,.mul,.dup 3,.dup 2,.div,.dup 3,.eq,.dup 4,.iszero,.or] ++ assertTop ++ [.swap 2,.pop,.pop]) := by
  first | rfl | decide | omega | simp only [selected,binaryCode,binTail,uTail]

#print axioms value
#print axioms selected
#print axioms public_selection
#print axioms original_guard
end Solidity.Backend.PrimitivePackets.CheckedMul
