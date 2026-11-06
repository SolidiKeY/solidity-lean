import Solidity.Lowering.V08.EnvironmentProjection
import Solidity.Lowering.V08.AbiObservations

/-!
# Fixed Keccak observation transport

Read-only use of the existing Keccak output format, G01 fixed hash observation
and intrinsic keccakBytes. No implementation, precompile adapter or collision
assumption is added. Source execution/application remains separate.
-/
namespace Solidity.Lowering.V08.CryptoObservations
open Solidity

/-- A bounded byte fold, with arbitrary initial accumulator and input length. -/
theorem fold_byte_bound (bytes : List Nat) (bounded : ∀ byte, byte ∈ bytes → byte < 256)
    (initial : Nat) :
    bytes.foldl (fun accumulator byte => 256 * accumulator + byte) initial <
      (initial + 1) * 256 ^ bytes.length := by
  induction bytes generalizing initial with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.pow_zero, Nat.mul_one]; omega
  | cons byte rest ih =>
    have byteBound := bounded byte (List.mem_cons_self)
    have restBound : ∀ item, item ∈ rest → item < 256 :=
      fun item member => bounded item (List.mem_cons_of_mem byte member)
    have nextBound : 256 * initial + byte + 1 ≤ 256 * (initial + 1) := by omega
    change rest.foldl _ (256 * initial + byte) < (initial + 1) * 256 ^ (rest.length + 1)
    calc
      _ < (256 * initial + byte + 1) * 256 ^ rest.length := ih restBound _
      _ ≤ (256 * (initial + 1)) * 256 ^ rest.length := Nat.mul_le_mul_right _ nextBound
      _ = (initial + 1) * 256 ^ (rest.length + 1) := by rw [Nat.pow_succ]; ac_rfl

/-- Existing big-endian byte accumulation never exceeds its represented width. -/
theorem ofBytes_bound (bytes : List Nat) (bounded : ∀ byte, byte ∈ bytes → byte < 256) :
    Keccak.ofBytes bytes < 256 ^ bytes.length := by
  simpa only [Keccak.ofBytes, Nat.zero_add, Nat.one_mul] using fold_byte_bound bytes bounded 0

/-- The published sponge emits at most four lanes of eight bytes. No bound on
message length, lane values or intermediate hash state is assumed. -/
theorem keccak_length_bound (bytes : List Nat) : (Keccak.keccak256 bytes).length ≤ 32 := by
  simp only [Keccak.keccak256, Keccak.sponge, List.length_flatten, List.map_map,
    Function.comp_def, List.length_map, List.length_range, List.map_const',
    List.sum_replicate_nat, List.length_take]
  omega

/-- Every emitted byte is reduced by the existing implementation modulo256. -/
theorem keccak_bytes_bound (bytes : List Nat) :
    ∀ byte, byte ∈ Keccak.keccak256 bytes → byte < 256 := by
  intro byte member
  unfold Keccak.keccak256 Keccak.sponge at member
  obtain ⟨block, memberBlock, memberByte⟩ := List.mem_flatten.mp member
  obtain ⟨word, _, same⟩ := List.mem_map.mp memberBlock
  subst block
  obtain ⟨index, _, same⟩ := List.mem_map.mp memberByte
  subst byte
  exact Nat.mod_lt _ (by decide +kernel)

/-- The actual published Keccak numeric result is a word, not an added premise. -/
theorem keccak_word_bound (bytes : List Nat) : Keccak.keccak256Nat bytes < 2 ^ 256 := by
  have bound := ofBytes_bound (Keccak.keccak256 bytes) (keccak_bytes_bound bytes)
  have width := Nat.pow_le_pow_right (by decide +kernel : 1 ≤ 256) (keccak_length_bound bytes)
  have power : (256 : Nat) ^ 32 = 2 ^ 256 := by decide +kernel
  rw [power] at width
  exact Nat.lt_of_lt_of_le bound width

/-- Existing intrinsic byte normalization retains every source UInt8 exactly. -/
theorem byte_input_normalize (bytes : List UInt8) :
    (bytes.map (fun byte => (byte.toNat : Int))).map (fun byte => byte.toNat % 256) =
      bytes.map UInt8.toNat := by
  rw [List.map_map]
  apply List.map_congr_left
  intro byte _
  change byte.toNat % 256 = byte.toNat
  exact Nat.mod_eq_of_lt byte.toNat_lt

/-- The supplied G01 Keccak pin's actual fixed observation agrees with the
intrinsic byte hash. The raw hash bound is proved above, not assumed. F.Keccak
is the published pin contract; this does not prove source expression execution. -/
theorem fixed_keccak_observation (fixed : Roadmap.Fixed) (pin : fixed.Keccak)
    (bytes : List UInt8) :
    EnvironmentProjection.liftWord (fixed.hash bytes) =
      keccakBytes (bytes.map (fun byte => (byte.toNat : Int))) := by
  apply Subtype.ext
  change (fixed.evm.keccak bytes : Int) = _
  rw [pin.1 bytes]
  unfold Roadmap.Evm.keccakWord
  rw [Nat.mod_eq_of_lt (keccak_word_bound _)]
  unfold keccakBytes
  simp only [byte_input_normalize, dif_pos (keccak_word_bound _)]

/-- The existing source ABI word observation of the fixed hash is exactly the
intrinsic word emission of its actual typed hash result. -/
theorem fixed_keccak_bytes (fixed : Roadmap.Fixed) (pin : fixed.Keccak)
    (bytes : List UInt8) :
    Source.wordBytes (fixed.hash bytes) =
      Semantics.wordBytes (keccakBytes (bytes.map (fun byte => (byte.toNat : Int)))).1.toNat := by
  have number : (keccakBytes (bytes.map (fun byte => (byte.toNat : Int)))).1.toNat =
      (fixed.hash bytes).val := by
    rw [← fixed_keccak_observation fixed pin bytes]
    exact Int.toNat_natCast _
  rw [number, wordBytes_transport]

#print axioms fixed_keccak_bytes
#print axioms fold_byte_bound
#print axioms ofBytes_bound
#print axioms keccak_length_bound
#print axioms keccak_bytes_bound
#print axioms keccak_word_bound
#print axioms byte_input_normalize
#print axioms fixed_keccak_observation
end Solidity.Lowering.V08.CryptoObservations
