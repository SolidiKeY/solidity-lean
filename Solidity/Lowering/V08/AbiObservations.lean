import Solidity.Source.Observe
import Solidity.Semantics.RevertData

/-!
# Independent source and intrinsic ABI observation agreement

The two published byte encodings are compared directly. No source execution is
defined using an emitted target, and no decoder or payload emitter is added.
-/
namespace Solidity.Lowering.V08

/-- The independent recursive big-endian source layout agrees with the
intrinsic position-based layout at every byte length, without a word bound. -/
theorem beBytes_layout (length number : Nat) :
    Source.beBytes length number = (List.range length).map
      (fun index => UInt8.ofNat (number / 256 ^ (length - 1 - index) % 256)) := by
  induction length generalizing number with
  | zero => rfl
  | succ length ih =>
    simp only [Source.beBytes, ih, List.range_succ, List.map_append,
      List.map_cons, List.map_nil]
    congr 1
    · apply List.map_congr_left
      intro index member
      have lt : index < length := List.mem_range.mp member
      have exponent : length - index = (length - 1 - index) + 1 := by omega
      simp only [Nat.add_sub_cancel, Nat.div_div_eq_div_mul]
      rw [exponent, Nat.pow_succ']
    · simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.pow_zero, Nat.div_one]

/-- Word bytes agree between independent source values and intrinsic payloads. -/
theorem wordBytes_transport (word : Roadmap.Word) :
    Source.wordBytes word = Semantics.wordBytes word.val :=
  beBytes_layout 32 word.val

/-- Padding is identical, including empty and non-word-aligned messages. -/
theorem pad32_transport (bytes : Roadmap.Bytes) :
    Source.pad32 bytes = Semantics.pad32 bytes := rfl

/-- Every in-profile panic code retains its exact selector and ABI word. -/
theorem panicData_transport (code : Source.PanicCode) :
    Source.panicData code = Semantics.encodePanic code.code := by
  have bound : code.code < 2 ^ 256 := by cases code <;> decide +kernel
  unfold Source.panicData Semantics.encodePanic
  rw [wordBytes_transport]
  simp only [Source.toWord, Nat.mod_eq_of_lt bound]
  rfl

/-- Revert reasons retain all bytes. The explicit ABI length bound is not a
source execution certificate and is not hidden in a decoder assumption. -/
theorem errorData_transport (bytes : Roadmap.Bytes) (bound : bytes.length < 2 ^ 256) :
    Source.errorData bytes = Semantics.encodeError bytes := by
  unfold Source.errorData Semantics.encodeError
  rw [wordBytes_transport, wordBytes_transport, pad32_transport]
  simp only [Source.toWord, Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt (show 32 < 2 ^ 256 by decide +kernel)]
  rfl

/-- The existing catch decoder returns the same result on source and intrinsic bytes. -/
theorem catch_error_transport (bytes : Roadmap.Bytes) (bound : bytes.length < 2 ^ 256) :
    Semantics.decodeError (Source.errorData bytes) =
      Semantics.decodeError (Semantics.encodeError bytes) :=
  congrArg Semantics.decodeError (errorData_transport bytes bound)

/-- Distinct source panic codes remain distinguishable intrinsic payloads. -/
theorem panic_payload_injective {left right : Source.PanicCode}
    (same : Semantics.encodePanic left.code = Semantics.encodePanic right.code) : left = right := by
  apply Source.panic_distinct
  unfold Source.revertOutcome
  rw [panicData_transport, panicData_transport, same]

/-- Sequences of already-typed words preserve their complete byte stream.
This is observation composition, not a new aggregate ABI emitter. -/
theorem wordSequence_transport (words : List Roadmap.Word) :
    words.flatMap Source.wordBytes =
      words.flatMap (fun word => Semantics.wordBytes word.val) := by
  have encoders : Source.wordBytes = (fun word : Roadmap.Word => Semantics.wordBytes word.val) :=
    funext wordBytes_transport
  exact congrArg (fun encoder : Roadmap.Word → Roadmap.Bytes => words.flatMap encoder) encoders

/-- Truncating to the represented byte width leaves every encoded byte intact. -/
theorem beBytes_mod (length number : Nat) :
    Source.beBytes length (number % 256 ^ length) = Source.beBytes length number := by
  induction length generalizing number with
  | zero => rfl
  | succ length ih =>
    simp only [Source.beBytes, Nat.pow_succ', Nat.mod_mul_right_div_self,
      Nat.mod_mul_right_mod, ih]

/-- Source word normalization and intrinsic low-word emission agree for every
natural number, without a range premise. -/
theorem natWordBytes_transport (number : Nat) :
    Source.wordBytes (Source.toWord number) = Semantics.wordBytes number := by
  change Source.beBytes 32 (number % 2 ^ 256) = Semantics.wordBytes number
  have power : (256 : Nat) ^ 32 = 2 ^ 256 := by decide +kernel
  rw [← power, beBytes_mod]
  exact beBytes_layout 32 number

/-- Exact reason-byte transport for arbitrary lists. Both published encoders
represent the length word modulo 2^256, so no new admission bound is required. -/
theorem errorData_transport_total (bytes : Roadmap.Bytes) :
    Source.errorData bytes = Semantics.encodeError bytes := by
  unfold Source.errorData Semantics.encodeError
  rw [natWordBytes_transport, natWordBytes_transport, pad32_transport]
  rfl

/-- The existing reason decoder returns the same result for every source reason. -/
theorem catch_error_transport_total (bytes : Roadmap.Bytes) :
    Semantics.decodeError (Source.errorData bytes) =
      Semantics.decodeError (Semantics.encodeError bytes) :=
  congrArg Semantics.decodeError (errorData_transport_total bytes)

end Solidity.Lowering.V08
