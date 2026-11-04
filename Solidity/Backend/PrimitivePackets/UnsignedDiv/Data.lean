import Solidity.Source.Machine
import Solidity.Backend.Scalar.Division

/-! Intrinsic uint256 local operands for the reserved unsigned div/mod packet.
These are existing Source and scoped-model terms, not a new source language.
No storage/layout/calldata or whole-program association is asserted. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedDiv

abbrev Uint := PrimTy.uint.Denote
abbrev sourceContext (Γ : Source.RCtx) := Source.STy.int Source.IntTy.u256 :: .int Source.IntTy.u256 :: Γ
abbrev modelContext (Γ : Solidity.Ctx) := LTy.val .uint :: .val .uint :: Γ

/-- Derive the source range from the actual intrinsic model value. -/
def sourceUInt (D : Source.Layout) (v : Uint) : Source.Val D (.int Source.IntTy.u256) :=
  .int v.val (by
    have hv : 0 ≤ v.val ∧ v.val < ((2 ^ 256 : Nat) : Int) := Scalar.uint_range v
    change 0 ≤ v.val ∧ v.val ≤ (2 ^ 256 : Nat) - 1
    omega)

def sourceLocals {D : Source.Layout} {Γ : Source.RCtx}
    (a d : Uint) (tail : Source.Locals D Γ) : Source.Locals D (sourceContext Γ) :=
  .cons (sourceUInt D a) (.cons (sourceUInt D d) tail)

def sourceDiv (E : Source.Env) (Γ : Source.RCtx) :
    Source.RExpr E (sourceContext Γ) (.int Source.IntTy.u256) :=
  .binary .div (.local .here) (.local (.there .here))

def sourceMod (E : Source.Env) (Γ : Source.RCtx) :
    Source.RExpr E (sourceContext Γ) (.int Source.IntTy.u256) :=
  .binary .mod (.local .here) (.local (.there .here))

def modelDiv (C : Contract) (Γ : Solidity.Ctx) : Solidity.Val C (modelContext Γ) .uint :=
  .binop .div rfl rfl (.simple (.local .here)) (.simple (.local (.there .here)))

def modelMod (C : Contract) (Γ : Solidity.Ctx) : Solidity.Val C (modelContext Γ) .uint :=
  .binop .mod rfl rfl (.simple (.local .here)) (.simple (.local (.there .here)))

end Solidity.Backend.PrimitivePackets.UnsignedDiv
