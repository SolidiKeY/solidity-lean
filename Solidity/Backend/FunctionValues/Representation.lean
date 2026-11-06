import Solidity.Backend.FunctionValues.Interface
import Solidity.Yul.Views.ScalarCodecs

/-! G42.05 runtime words reuse the published 24-byte source codec. Memory
here is the backend's explicit low-192-bit convention, not Source.Val.word
(which does not support external functions), nor an ABI alignment theorem. -/
namespace Solidity.Backend.FunctionValues
open Solidity.Source Solidity.Roadmap
open Solidity.Yul.Views

abbrev codec (D : Layout) (ps rs : List STy) (m : Option Source.Mutability) :=
  externalFnCodec D ps rs m 0 (by decide)

def encode (value : Source.Val D (.fn true ps rs m)) : Fin Evm.W :=
  let raw := (codec D ps rs m).encode value
  ⟨raw.val, Nat.lt_trans raw.isLt (by decide)⟩

/-- Reject words with high bits set instead of silently discarding them. -/
def decode (D : Layout) (ps rs : List STy) (m : Option Source.Mutability)
    (word : Fin Evm.W) : Option (Source.Val D (.fn true ps rs m)) :=
  if h : word.val < 256 ^ 24 then (codec D ps rs m).decode ⟨word.val, h⟩ else none

theorem decode_encode (value : Source.Val D (.fn true ps rs m)) :
    decode D ps rs m (encode value) = some value := by
  exact dif_pos ((codec D ps rs m).encode value).isLt |>.trans
    ((codec D ps rs m).decode_encode value)

theorem encode_injective {a b : Source.Val D (.fn true ps rs m)}
    (equal : encode a = encode b) : a = b := by
  have decoded := congrArg (decode D ps rs m) equal
  rw [decode_encode, decode_encode] at decoded
  exact Option.some.inj decoded

theorem encode_represents (value : ExternalValue D ps rs m) :
    Represents value.source (encode value.source) := by
  exact ⟨value, rfl, rfl⟩

theorem source_key (value : ExternalValue D ps rs m) :
    value.source.key = some (Int.ofNat value.number) := by
  rfl

theorem address_projection (value : ExternalValue D ps rs m) :
    (encode value.source).val / 2 ^ 32 = value.address.val := by
  have hs := scalar_beValue_bound value.selector
  rw [value.selector_length] at hs
  change (value.address.val * 2 ^ 32 + Source.beValue value.selector) / 2 ^ 32 = _
  omega

theorem selector_projection (value : ExternalValue D ps rs m) :
    Source.beBytes 4 ((encode value.source).val % 2 ^ 32) = value.selector := by
  have hs := scalar_beValue_bound value.selector
  rw [value.selector_length] at hs
  have remainder : (encode value.source).val % 2 ^ 32 = Source.beValue value.selector := by
    change (value.address.val * 2 ^ 32 + Source.beValue value.selector) % 2 ^ 32 = _
    omega
  rw [remainder, ← value.selector_length]
  exact scalar_beBytes_value value.selector

theorem high_bits_refused (word : Fin Evm.W) (high : 256 ^ 24 ≤ word.val) :
    decode D ps rs m word = none := by
  exact dif_neg (Nat.not_lt.mpr high)

end Solidity.Backend.FunctionValues
