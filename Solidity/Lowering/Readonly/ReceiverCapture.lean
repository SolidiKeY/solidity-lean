import Solidity.Lowering.Readonly.CapturedArguments
import Solidity.Roadmap.Contracts

/-! Faithful receiver transport at the source capture boundary. Addresses
remain arbitrary160-bit values; no self/code/static/provenance assumption is
inferred from their numeric embedding. This does not lower CALL/STATICCALL. -/
namespace Solidity.Lowering.Readonly.ReceiverCapture
open Solidity.Roadmap (Address)

def word (address : Address) : PrimTy.uint.Denote :=
  Solidity.lenU address.val
    (Nat.lt_of_lt_of_le address.isLt (Solidity.Source.two_pow_le (by decide : 160 ≤ 256)))

theorem exact_value (address : Address) : (word address).val = Int.ofNat address.val := rfl

theorem faithful : Function.Injective word := by
  intro left right same
  apply Fin.ext
  exact Int.ofNat.inj (congrArg Subtype.val same)

def value {C : Contract} {Γ : Ctx} (address : Address) : Solidity.Val C Γ .uint :=
  CapturedArguments.literal .uint (word address)

theorem evaluate {C : Contract} {Γ : Ctx} (state : State C Γ) (address : Address) :
    (value address).evalT state = .ok (word address) :=
  CapturedArguments.literal_eval state .uint (word address)

/-- A previously captured receiver is insensitive to later caller mutations,
including changes to the local used to compute that receiver. -/
theorem stable {C : Contract} {Γ : Ctx} (first second : State C Γ) (address : Address) :
    (value address).evalT first = .ok (word address) ∧
    (value address).evalT second = .ok (word address) :=
  ⟨evaluate first address, evaluate second address⟩

end Solidity.Lowering.Readonly.ReceiverCapture
