import Solidity.RevertBytes

/-!
# Exact observations of the published Error(string) codec

These are laws of Semantics.encodeError/pad32, not another ABI semantics.
No aggregate signature or calldata acceptance predicate is restricted here.
This independent backfill does not establish G40 or G41 compilation.
-/
namespace Solidity.Backend.AbiWorld
open Semantics

/-- A published ABI word occupies exactly 32 bytes. -/
theorem word_length (n : Nat) : (wordBytes n).length = 32 := by
  simp only [wordBytes, List.length_map, List.length_range]

/-- Padding has its exact length, with no bound on the input list. -/
theorem padded_length (bs : List UInt8) :
    (pad32 bs).length = bs.length + (32 - bs.length % 32) % 32 := by
  simp only [pad32, List.length_append, List.length_replicate]

/-- Padding is word aligned for every input length, including zero. -/
theorem padded_alignment (bs : List UInt8) : (pad32 bs).length % 32 = 0 := by
  rw [padded_length]
  have h : bs.length % 32 < 32 := Nat.mod_lt _ (by decide)
  omega

/-- Padding adds fewer than one word and never truncates the payload. -/
theorem padded_bounds (bs : List UInt8) :
    bs.length ≤ (pad32 bs).length ∧ (pad32 bs).length < bs.length + 32 := by
  rw [padded_length]
  have h : (32 - bs.length % 32) % 32 < 32 := Nat.mod_lt _ (by decide)
  omega

/-- The unpadded bytes survive exactly, including nonzero boundary bytes. -/
theorem padded_payload (bs : List UInt8) : (pad32 bs).take bs.length = bs := by
  exact List.take_left

/-- Every added byte is zero. -/
theorem padded_suffix (bs : List UInt8) :
    (pad32 bs).drop bs.length = List.replicate ((32 - bs.length % 32) % 32) 0 := by
  exact List.drop_left

/-- The string starts at byte 68, after selector, offset and length. -/
theorem error_tail (bs : List UInt8) : (encodeError bs).drop 68 = pad32 bs := by
  unfold encodeError
  apply List.drop_left'
  simp only [List.length_append, errorSelector, List.length_cons, List.length_nil, word_length]

/-- The published offset word is exactly 32, at byte 4. -/
theorem error_offset (bs : List UInt8) :
    ((encodeError bs).drop 4).take 32 = wordBytes 32 := by
  simp only [encodeError, List.append_assoc]
  have hd : (errorSelector ++ (wordBytes 32 ++ (wordBytes bs.length ++ pad32 bs))).drop 4 =
      wordBytes 32 ++ (wordBytes bs.length ++ pad32 bs) := List.drop_left' (by decide)
  rw [hd]
  exact List.take_left' (word_length 32)

/-- The published length word occurs at byte 36, independent of the payload. -/
theorem error_length_word (bs : List UInt8) :
    ((encodeError bs).drop 36).take 32 = wordBytes bs.length := by
  unfold encodeError
  have hd : ((errorSelector ++ wordBytes 32) ++ (wordBytes bs.length ++ pad32 bs)).drop 36 =
      wordBytes bs.length ++ pad32 bs := by
    apply List.drop_left'
    simp only [List.length_append, errorSelector, List.length_cons, List.length_nil, word_length]
  rw [List.append_assoc (errorSelector ++ wordBytes 32), hd]
  exact List.take_left' (word_length bs.length)

/-- Exact payload observation in the original encoded packet. -/
theorem error_payload (bs : List UInt8) :
    ((encodeError bs).drop 68).take bs.length = bs := by
  rw [error_tail, padded_payload]

/-- Appending a later packet cannot alter any byte in the first packet. -/
theorem packet_prefix (packet suffix : List UInt8) :
    (packet ++ suffix).take packet.length = packet := List.take_left

/-- Pointwise noninterference applies to every byte, not just aligned words. -/
theorem packet_byte (packet suffix : List UInt8) (i : Nat) (hi : i < packet.length) :
    (packet ++ suffix)[i]? = packet[i]? := List.getElem?_append_left hi

/-- Padding is injective once the original lengths are known. -/
theorem padded_injective (xs ys : List UInt8) (hlen : xs.length = ys.length)
    (h : pad32 xs = pad32 ys) : xs = ys := by
  have ht : (pad32 xs).take xs.length = (pad32 ys).take xs.length := congrArg (List.take xs.length) h
  rw [padded_payload, hlen, padded_payload] at ht
  exact ht

/-- The entire Error packet is four selector bytes plus an aligned ABI body. -/
theorem error_body_alignment (bs : List UInt8) : (encodeError bs).length % 32 = 4 := by
  have hp : (pad32 bs).length % 32 = 0 := padded_alignment bs
  have hl : (encodeError bs).length = 68 + (pad32 bs).length := by
    simp only [encodeError, List.length_append, errorSelector, List.length_cons,
      List.length_nil, word_length]
  omega

/-- info: 'Solidity.Backend.AbiWorld.padded_alignment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms padded_alignment
/-- info: 'Solidity.Backend.AbiWorld.error_payload' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms error_payload
/-- info: 'Solidity.Backend.AbiWorld.packet_byte' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms packet_byte
end Solidity.Backend.AbiWorld
