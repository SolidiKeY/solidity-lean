import Solidity.Backend.AbiWorld.ErrorLayout
import Solidity.Backend.Failure.Immediate

/-! Relate the published codec words to existing machine numerals; no new codec. -/
namespace Solidity.Backend.AbiWorld
open Semantics Failure

/-- Byte observation of the existing machine numeral, at every width. -/
theorem numeral_byte (k n i : Nat) (hi : i < k) :
    (digits k n)[i]'(by rw [digits_length]; exact hi) =
      UInt8.ofNat (n / 256 ^ (k - 1 - i) % 256) := by
  induction k generalizing n i with
  | zero => omega
  | succ k ih =>
    change ((digits k (n / 256)) ++ [UInt8.ofNat (n % 256)])[i]'(by simp only [List.length_append, digits_length, List.length_singleton]; exact hi) = _
    by_cases hik : i < k
    · rw [List.getElem_append_left (by rw [digits_length]; exact hik), ih _ _ hik]
      rw [Nat.div_div_eq_div_mul]
      have he : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
      rw [he, Nat.pow_succ, Nat.mul_comm 256]
    · have he : i = k := by omega
      subst i
      rw [List.getElem_append_right (by rw [digits_length]; exact Nat.le_refl k)]
      simp only [digits_length,
        Nat.sub_self, List.getElem_cons_zero, Nat.add_sub_cancel, Nat.pow_zero, Nat.div_one]

/-- Existing numerals preserve exactly their low width bytes for arbitrary natural-number inputs. -/
theorem numeral_mod (k n : Nat) : digits k (n % 256 ^ k) = digits k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [digits, Nat.pow_succ, Nat.mod_mul_left_div_self, Nat.mod_mul_left_mod, ih]

/-- The codec's existing word bytes equal the machine's existing numeral bytes. -/
theorem word_eq_numeral (n : Nat) : wordBytes n = digits 32 n := by
  apply List.ext_getElem (by rw [word_length, digits_length])
  intro i hi hj
  have h : i < 32 := by simpa only [word_length] using hi
  simp only [wordBytes, List.getElem_map, List.getElem_range]
  rw [numeral_byte 32 n i h]

/-- Arbitrary ABI words roundtrip without a new decoder definition. -/
theorem read_word (n : Nat) (hn : n < 256 ^ 32) : bytesNat (wordBytes n) = n := by
  rw [word_eq_numeral]
  exact read_digits 32 n hn

/-- All representable Error(string) lengths roundtrip in the published decoder.
The bound is the ABI word's representability bound, not a fixed test budget. -/
theorem error_roundtrip (bs : List UInt8) (hlen : bs.length < 256 ^ 32) :
    decodeError (encodeError bs) = some bs := by
  have hsel : (encodeError bs).take 4 = errorSelector := by
    simp only [encodeError, List.append_assoc]
    exact List.take_left' (by decide)
  have hbody : (encodeError bs).drop 4 = wordBytes 32 ++ (wordBytes bs.length ++ pad32 bs) := by
    simp only [encodeError, List.append_assoc]
    exact List.drop_left' (by decide)
  have hhead : (wordBytes 32 ++ (wordBytes bs.length ++ pad32 bs)).take 32 = wordBytes 32 :=
    List.take_left' (word_length 32)
  have hrest : (wordBytes 32 ++ (wordBytes bs.length ++ pad32 bs)).drop 32 =
      wordBytes bs.length ++ pad32 bs := List.drop_left' (word_length 32)
  have hlenword : (wordBytes bs.length ++ pad32 bs).take 32 = wordBytes bs.length :=
    List.take_left' (word_length bs.length)
  have hdata : (wordBytes bs.length ++ pad32 bs).drop 32 = pad32 bs :=
    List.drop_left' (word_length bs.length)
  have hb : ¬ (wordBytes 32 ++ (wordBytes bs.length ++ pad32 bs)).length < 32 := by
    simp only [List.length_append, word_length]
    omega
  have hr : ¬ (wordBytes bs.length ++ pad32 bs).length < 32 := by
    simp only [List.length_append, word_length]
    omega
  simp only [decodeError, hsel, ite_true, hbody, hhead, read_word 32 (by decide), hrest,
    hb, hr, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    hlenword, read_word bs.length hlen, hdata, padded_payload]

/-- info: 'Solidity.Backend.AbiWorld.read_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_word
/-- info: 'Solidity.Backend.AbiWorld.error_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms error_roundtrip
end Solidity.Backend.AbiWorld
