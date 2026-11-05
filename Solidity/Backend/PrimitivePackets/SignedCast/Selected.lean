import Solidity.Backend.PrimitivePackets.SignedCast.CastSource
import Solidity.Evm.MemoryCompile

/-! Selection is the existing public memory compiler, with no supplied code
certificate or desired execution premise. -/
namespace Solidity.Backend.PrimitivePackets.SignedCast
open Evm Evm.Memory Solidity.Lowering.V07

def value {C : Contract} {Γ : Ctx} (bits : Nat) (i : Idx Γ (.val .int)) : Val C Γ .int :=
  SignedWidthCasts.castValue bits (.simple (.local i))

theorem selection_exists {C : Contract} {Γ : Ctx} (bits : Nat) (valid : Valid bits)
    (offset : Nat) (F : Frag Γ) (i : Idx Γ (.val .int)) :
    (Memory.compileVal offset F (value (C:=C) bits i)).isSome = true := by
  have widths : bits = 8 ∨ bits = 16 ∨ bits = 24 ∨ bits = 32 ∨ bits = 40 ∨ bits = 48 ∨ bits = 56 ∨ bits = 64 ∨ bits = 72 ∨ bits = 80 ∨ bits = 88 ∨ bits = 96 ∨ bits = 104 ∨ bits = 112 ∨ bits = 120 ∨ bits = 128 ∨ bits = 136 ∨ bits = 144 ∨ bits = 152 ∨ bits = 160 ∨ bits = 168 ∨ bits = 176 ∨ bits = 184 ∨ bits = 192 ∨ bits = 200 ∨ bits = 208 ∨ bits = 216 ∨ bits = 224 ∨ bits = 232 ∨ bits = 240 ∨ bits = 248 ∨ bits = 256 := by
    rcases valid with ⟨byte,lo,hi⟩
    omega
  rcases widths with h8 | h16 | h24 | h32 | h40 | h48 | h56 | h64 | h72 | h80 | h88 | h96 | h104 | h112 | h120 | h128 | h136 | h144 | h152 | h160 | h168 | h176 | h184 | h192 | h200 | h208 | h216 | h224 | h232 | h240 | h248 | h256 <;> subst bits <;> rfl

def selected {C : Contract} {Γ : Ctx} (bits : Nat) (valid : Valid bits) (offset : Nat) (F : Frag Γ)
    (i : Idx Γ (.val .int)) : CompiledVal offset F (value (C:=C) bits i) :=
  (Memory.compileVal offset F (value bits i)).get (selection_exists bits valid offset F i)

theorem public_selection {C : Contract} {Γ : Ctx} (bits : Nat) (valid : Valid bits) (offset : Nat) (F : Frag Γ)
    (i : Idx Γ (.val .int)) :
    Memory.compileVal offset F (value (C:=C) bits i) = some (selected bits valid offset F i) := by
  first | rfl | simp only [selected, Option.some_get]
end Solidity.Backend.PrimitivePackets.SignedCast
