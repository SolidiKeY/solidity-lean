import Solidity.Language.FixedPoint.Laws

/-!
# Fixed-point ABI encoding

The ABI specification encodes `fixed<M>x<N>` / `ufixed<M>x<N>` as the
value `v / 10^N` through its scaled integer `v`, a 32-byte big-endian
two's-complement word as for `int256` / `uint256` (`abi-spec.rst:213–221`
at `v0.8.38`), and names a type in a selector by its canonical name, the
aliases `fixed` / `ufixed` as `fixed128x18` / `ufixed128x18`
(`abi-spec.rst:71–72`).  solc 0.8.38 generates no ABI code for these types
(its cleanup and validation functions are unimplemented for them), so the
coder behaviour below is a proposal by analogy with `intM` / `uintM` (P5),
not compiler behaviour; `docs/feature-work/fixed-point-semantics.md`, §6.3,
records the reading.

* `Fx.encode` — the word; `Fx.abiEncode` — its 32 big-endian bytes.
* `Fx.decodeV2` — ABI coder v2 decoding: a word whose upper bits are not
  the sign- or zero-extension of an `M`-bit integer reverts (`none`), as
  solc's v2 validator does for `intM` / `uintM` (`decodeV2_isSome_iff`).
  Decoding is exactly the inverse of `encode`: `Fx.decodeV2_encode`,
  `Fx.encode_of_decodeV2`, `Fx.decodeV2_eq_none_iff`.
* `Fx.decodeV1` — ABI coder v1 (the legacy pipeline's pragma may select
  it; G00 Q4): no validation, the low `M` bits cleaned as v1 cleans `intM`;
  `Fx.decodeV1_of_decodeV2` (the coders agree on clean words).
* `Fx.encodePacked` — `abi.encodePacked` of a top-level argument: the
  `M/8`-byte two's complement, unpadded (`abi-spec.rst:755`); there is no
  packed decoder in Solidity, and `Fx.ofPackedBytes` only witnesses that
  the encoding loses nothing.
* The type names include `N = 0` (`fixedMx0`, P4), which the ABI
  specification excludes (`0 < N`, `abi-spec.rst:66–67`): a deliberate
  extension, since solc's scanner admits the types.
-/

namespace Solidity.Language.FixedPoint

/-! ### Big-endian bytes -/

/-- `n` modulo `256^k` as `k` big-endian bytes. -/
def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => beBytes k (n / 256) ++ [UInt8.ofNat (n % 256)]

/-- Bytes read big-endian. -/
def beNat (bs : List UInt8) : Nat := bs.foldl (fun a b => a * 256 + b.toNat) 0

theorem beBytes_length : ∀ k n, (beBytes k n).length = k
  | 0, _ => rfl
  | k + 1, n => by
    simp only [beBytes, List.length_append, List.length_singleton, beBytes_length k (n / 256)]

theorem beNat_append_single (bs : List UInt8) (b : UInt8) :
    beNat (bs ++ [b]) = beNat bs * 256 + b.toNat := by
  simp only [beNat, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem beNat_beBytes : ∀ k n, beNat (beBytes k n) = n % 256 ^ k
  | 0, n => by simp only [beBytes, beNat, List.foldl_nil, Nat.pow_zero, Nat.mod_one]
  | k + 1, n => by
    simp only [beBytes, beNat_append_single, beNat_beBytes k (n / 256), UInt8.toNat_ofNat']
    have hm : n % (256 * 256 ^ k) = n % 256 + 256 * (n / 256 % 256 ^ k) := Nat.mod_mul
    have hp : 256 ^ (k + 1) = 256 * 256 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have h8 : (2 : Nat) ^ 8 = 256 := by decide
    rw [hp, hm, h8, Nat.mod_mod]
    omega

theorem beNat_lt_aux : ∀ (bs : List UInt8) (acc : Nat),
    bs.foldl (fun a b => a * 256 + b.toNat) acc < (acc + 1) * 256 ^ bs.length
  | [], acc => by simp only [List.foldl_nil, List.length_nil, Nat.pow_zero, Nat.mul_one]; omega
  | b :: bs, acc => by
    simp only [List.foldl_cons, List.length_cons]
    have ih : bs.foldl (fun a b => a * 256 + b.toNat) (acc * 256 + b.toNat) <
        (acc * 256 + b.toNat + 1) * 256 ^ bs.length := beNat_lt_aux bs _
    have hb : b.toNat < 256 := b.toNat_lt
    have hp : 256 ^ (bs.length + 1) = 256 ^ bs.length * 256 := by rw [Nat.pow_succ]
    have h1 : acc * 256 + b.toNat + 1 ≤ (acc + 1) * 256 := by omega
    have h2 : (acc * 256 + b.toNat + 1) * 256 ^ bs.length ≤ (acc + 1) * 256 * 256 ^ bs.length :=
      Nat.mul_le_mul_right _ h1
    have h3 : (acc + 1) * 256 * 256 ^ bs.length = (acc + 1) * (256 ^ bs.length * 256) := by
      rw [Nat.mul_assoc, Nat.mul_comm 256]
    rw [hp]
    omega

theorem beNat_lt (bs : List UInt8) : beNat bs < 256 ^ bs.length := by
  have h : beNat bs < (0 + 1) * 256 ^ bs.length := beNat_lt_aux bs 0
  omega

theorem beBytes_foldl : ∀ (bs : List UInt8) (k acc : Nat),
    beBytes (k + bs.length) (bs.foldl (fun a b => a * 256 + b.toNat) acc) = beBytes k acc ++ bs
  | [], k, acc => by simp only [List.length_nil, Nat.add_zero, List.foldl_nil, List.append_nil]
  | b :: bs, k, acc => by
    have hb : b.toNat < 256 := b.toNat_lt
    have hd : (acc * 256 + b.toNat) / 256 = acc := by omega
    have hm : (acc * 256 + b.toNat) % 256 = b.toNat := by omega
    have ih : beBytes (k + 1 + bs.length)
        (bs.foldl (fun a b => a * 256 + b.toNat) (acc * 256 + b.toNat)) =
        beBytes (k + 1) (acc * 256 + b.toNat) ++ bs := beBytes_foldl bs (k + 1) _
    have hk : k + (b :: bs).length = k + 1 + bs.length := by
      simp only [List.length_cons]; omega
    simp only [List.foldl_cons, hk, ih, beBytes, hd, hm, UInt8.ofNat_toNat, List.append_assoc,
      List.singleton_append]

/-- Bytes read and written back are the bytes. -/
theorem beBytes_beNat (bs : List UInt8) : beBytes bs.length (beNat bs) = bs := by
  have h : beBytes (0 + bs.length) (bs.foldl (fun a b => a * 256 + b.toNat) 0) =
      beBytes 0 0 ++ bs := beBytes_foldl bs 0 0
  simp only [Nat.zero_add, beBytes, List.nil_append] at h
  exact h

theorem pow_256 : (256 : Nat) ^ 32 = 2 ^ 256 := by
  rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]

/-- `2^M = 256^(M/8)`. -/
theorem pow_bits_bytes (t : FxTy) : (2 : Nat) ^ t.bits = 256 ^ (t.bits / 8) := by
  have h : (decide (8 ≤ t.bits) && decide (t.bits ≤ 256) && t.bits % 8 == 0 &&
      decide (t.digits ≤ 80)) = true := t.valid
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have hb : t.bits = 8 * (t.bits / 8) := by omega
  rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul, ← hb]

namespace Fx

variable {t : FxTy}

theorem ofInt?_val {v : Int} {a : Fx t} (h : ofInt? t v = some a) : a.1 = v := by
  unfold ofInt? at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
  · exact nomatch h

theorem ofInt?_isSome (t : FxTy) (v : Int) : (ofInt? t v).isSome = t.inRange v := by
  unfold ofInt?
  by_cases h : t.inRange v = true
  · simp only [h, dite_true, Option.isSome_some]
  · simp only [h, Bool.false_eq_true, dite_false, Option.isSome_none]

/-! ### Words -/

theorem toWord_toNat_lt (a : Fx t) : (toWord a).toNat < 2 ^ 256 := by
  have h : 0 ≤ toWord a ∧ toWord a < 2 ^ 256 := toWord_range a
  have hc : ((2 ^ 256 : Nat) : Int) = (2 : Int) ^ 256 := Int.natCast_pow 2 256
  have he : ((toWord a).toNat : Int) = toWord a := Int.toNat_of_nonneg h.1
  omega

/-- The ABI word of a value: its scaled integer, two's complement modulo
`2^256`. -/
def encode (a : Fx t) : Fin (2 ^ 256) := ⟨(toWord a).toNat, toWord_toNat_lt a⟩

theorem encode_val (a : Fx t) : ((encode a).val : Int) = toWord a :=
  Int.toNat_of_nonneg (toWord_range a).1

/-- ABI coder v2 decoding: the word read as `int256` where signed, then
range-checked; `none` (the decoder reverts) for dirty upper bits. -/
def decodeV2 (t : FxTy) (w : Fin (2 ^ 256)) : Option (Fx t) := ofWord? t (w.val : Int)

/-- Decoding the encoding gives the value back. -/
theorem decodeV2_encode (a : Fx t) : decodeV2 t (encode a) = some a := by
  simp only [decodeV2, encode_val]
  exact ofWord_toWord a

/-- Only the canonical word of a value decodes to it. -/
theorem encode_of_decodeV2 {w : Fin (2 ^ 256)} {a : Fx t} (h : decodeV2 t w = some a) :
    encode a = w := by
  have hw0 : (0 : Int) ≤ w.val := Int.natCast_nonneg _
  have hc : ((2 ^ 256 : Nat) : Int) = (2 : Int) ^ 256 := Int.natCast_pow 2 256
  have hw1 : (w.val : Int) < 2 ^ 256 := by
    have hl : w.val < 2 ^ 256 := w.isLt
    omega
  have hv : a.1 = (if t.signed ∧ 2 ^ 255 ≤ (w.val : Int) then (w.val : Int) - 2 ^ 256
      else (w.val : Int)) := ofInt?_val h
  have hm : a.1 % 2 ^ 256 = (w.val : Int) := by
    rw [hv]
    split
    · rw [Int.sub_emod_right]; exact Int.emod_eq_of_lt hw0 hw1
    · exact Int.emod_eq_of_lt hw0 hw1
  apply Fin.ext
  have he : ((encode a).val : Int) = (w.val : Int) := by rw [encode_val]; exact hm
  exact Int.ofNat_inj.mp he

/-- Every word that is not a value's encoding is rejected. -/
theorem decodeV2_eq_none_iff {w : Fin (2 ^ 256)} :
    decodeV2 t w = none ↔ ∀ a : Fx t, encode a ≠ w := by
  constructor
  · intro h a ha
    rw [← ha, decodeV2_encode] at h
    exact nomatch h
  · intro h
    cases hd : decodeV2 t w with
    | none => rfl
    | some a => exact absurd (encode_of_decodeV2 hd) (h a)

/-- The upper-bit condition: an unsigned word must be below `2^M`; a
signed word must be the sign extension of its low `M` bits (below
`2^(M-1)`, or at least `2^256 - 2^(M-1)`). -/
theorem decodeV2_isSome_iff (w : Fin (2 ^ 256)) :
    (decodeV2 t w).isSome = true ↔
      (if t.signed then w.val < 2 ^ (t.bits - 1) ∨ 2 ^ 256 - 2 ^ (t.bits - 1) ≤ w.val
       else w.val < 2 ^ t.bits) := by
  have hc : ((2 ^ 256 : Nat) : Int) = (2 : Int) ^ 256 := Int.natCast_pow 2 256
  have hc1 : ((2 ^ (t.bits - 1) : Nat) : Int) = (2 : Int) ^ (t.bits - 1) := Int.natCast_pow 2 _
  have hcb : ((2 ^ t.bits : Nat) : Int) = (2 : Int) ^ t.bits := Int.natCast_pow 2 _
  have hc255 : ((2 ^ 255 : Nat) : Int) = (2 : Int) ^ 255 := Int.natCast_pow 2 255
  have hw : w.val < 2 ^ 256 := w.isLt
  have hp : (2 : Int) ^ t.bits = 2 * 2 ^ (t.bits - 1) := t.pow_bits
  have hle : (2 : Int) ^ t.bits ≤ 2 ^ 256 := pow_bits_le t
  have h256 : (2 : Int) ^ 256 = 2 * 2 ^ 255 := by rw [Int.pow_succ, Int.mul_comm]
  have hdec : (decodeV2 t w).isSome = t.inRange
      (if t.signed ∧ 2 ^ 255 ≤ (w.val : Int) then (w.val : Int) - 2 ^ 256 else (w.val : Int)) :=
    ofInt?_isSome t _
  rw [hdec]
  simp only [FxTy.inRange, FxTy.lo, FxTy.hi, Bool.and_eq_true, decide_eq_true_eq]
  cases hs : t.signed
  · simp only [Bool.false_eq_true, false_and, if_false]
    omega
  · simp only [true_and, if_true]
    split <;> omega

/-! ### ABI coder v1 -/

/-- Wrapping depends only on the low `M` bits. -/
theorem wrapInt_emod_eq (t : FxTy) (v : Int) : wrapInt t (v % 2 ^ t.bits) = wrapInt t v := by
  unfold wrapInt
  simp only [Int.emod_emod]

/-- ABI coder v1 decoding: no validation; the low `M` bits are cleaned
(sign-extended where signed), as v1 cleans `intM` / `uintM`. -/
def decodeV1 (t : FxTy) (w : Fin (2 ^ 256)) : Fx t := wrap t (w.val : Int)

theorem decodeV1_eq_ofBits (w : Fin (2 ^ 256)) :
    decodeV1 t w = ofBits t ((w.val : Int) % 2 ^ t.bits) := by
  apply Subtype.ext
  simp only [decodeV1, ofBits, wrap, wrapInt_emod_eq]

/-- The two coders agree on every word v2 accepts. -/
theorem decodeV1_of_decodeV2 {w : Fin (2 ^ 256)} {a : Fx t} (h : decodeV2 t w = some a) :
    decodeV1 t w = a := by
  have he : encode a = w := encode_of_decodeV2 h
  rw [← he]
  apply Subtype.ext
  have hd : (2 : Int) ^ t.bits ∣ 2 ^ 256 := by
    have hb : t.bits ≤ 256 := t.bits_le
    exact ⟨2 ^ (256 - t.bits), by rw [← Int.pow_add, Nat.add_sub_cancel' hb]⟩
  have hm : a.1 % 2 ^ 256 % 2 ^ t.bits = a.1 % 2 ^ t.bits := Int.emod_emod_of_dvd a.1 hd
  have hw : wrapInt t (a.1 % 2 ^ 256) = wrapInt t a.1 := by
    rw [← wrapInt_emod_eq t (a.1 % 2 ^ 256), hm, wrapInt_emod_eq]
  simp only [decodeV1, wrap, encode_val, toWord, hw, wrapInt_of_inRange a.2]

/-- v1 decodes the encoding back too. -/
theorem decodeV1_encode (a : Fx t) : decodeV1 t (encode a) = a :=
  decodeV1_of_decodeV2 (decodeV2_encode a)

/-! ### Bytes -/

/-- `abi.encode(a)`: the word's 32 big-endian bytes. -/
def abiEncode (a : Fx t) : List UInt8 := beBytes 32 (encode a).val

theorem abiEncode_length (a : Fx t) : (abiEncode a).length = 32 := beBytes_length 32 _

/-- An isolated 32-byte head decoded at the type with coder v2 (solc's
decoder reads a head at an offset and ignores trailing data; offsets are
G40's). -/
def abiDecodeV2 (t : FxTy) (bs : List UInt8) : Option (Fx t) :=
  if bs.length = 32 then decodeV2 t ⟨beNat bs % 2 ^ 256, Nat.mod_lt _ (Nat.two_pow_pos 256)⟩
  else none

theorem beNat_mod_of_length {bs : List UInt8} (h : bs.length = 32) :
    beNat bs % 2 ^ 256 = beNat bs := by
  have hl : beNat bs < 256 ^ bs.length := beNat_lt bs
  rw [h, pow_256] at hl
  exact Nat.mod_eq_of_lt hl

theorem abiDecodeV2_abiEncode (a : Fx t) : abiDecodeV2 t (abiEncode a) = some a := by
  have hl : (abiEncode a).length = 32 := abiEncode_length a
  have hn : beNat (abiEncode a) % 2 ^ 256 = (encode a).val := by
    rw [beNat_mod_of_length hl]
    simp only [abiEncode, beNat_beBytes, pow_256]
    exact Nat.mod_eq_of_lt (encode a).isLt
  have hw : (⟨beNat (abiEncode a) % 2 ^ 256, Nat.mod_lt _ (Nat.two_pow_pos 256)⟩ :
      Fin (2 ^ 256)) = encode a := Fin.ext hn
  simp only [abiDecodeV2, hl, if_true, hw]
  exact decodeV2_encode a

/-- Only the canonical bytes of a value decode to it: every other 32-byte
head is rejected. -/
theorem abiEncode_of_abiDecodeV2 {bs : List UInt8} {a : Fx t}
    (h : abiDecodeV2 t bs = some a) : abiEncode a = bs := by
  unfold abiDecodeV2 at h
  by_cases hl : bs.length = 32
  · simp only [hl, if_true] at h
    have he : encode a = ⟨beNat bs % 2 ^ 256, Nat.mod_lt _ (Nat.two_pow_pos 256)⟩ :=
      encode_of_decodeV2 h
    have hb : beBytes bs.length (beNat bs) = bs := beBytes_beNat bs
    simp only [abiEncode, he, beNat_mod_of_length hl]
    rw [hl] at hb
    exact hb
  · simp only [hl, if_false] at h
    exact nomatch h

/-- `abi.encodePacked(a)`: the `M/8`-byte two's complement, unpadded. -/
def encodePacked (a : Fx t) : List UInt8 := beBytes (t.bits / 8) (toBits a).toNat

theorem encodePacked_length (a : Fx t) : (encodePacked a).length = t.bits / 8 :=
  beBytes_length _ _

/-- Packed bytes read back at the type, as their bit pattern: not an ABI
operation (Solidity has no packed decoder), only the inverse that shows
`encodePacked` loses nothing. -/
def ofPackedBytes (t : FxTy) (bs : List UInt8) : Option (Fx t) :=
  if bs.length = t.bits / 8 then some (ofBits t (beNat bs : Int)) else none

theorem ofPackedBytes_encodePacked (a : Fx t) : ofPackedBytes t (encodePacked a) = some a := by
  have hl : (encodePacked a).length = t.bits / 8 := encodePacked_length a
  have hp : (0 : Int) < 2 ^ t.bits := Int.pow_pos (by decide)
  have h0 : 0 ≤ toBits a := Int.emod_nonneg _ (by omega)
  have h1 : toBits a < 2 ^ t.bits := Int.emod_lt_of_pos _ hp
  have hcb : ((2 ^ t.bits : Nat) : Int) = (2 : Int) ^ t.bits := Int.natCast_pow 2 _
  have hn : (beNat (encodePacked a) : Int) = toBits a := by
    simp only [encodePacked, beNat_beBytes, ← pow_bits_bytes]
    have hlt : (toBits a).toNat < 2 ^ t.bits := by
      have he : ((toBits a).toNat : Int) = toBits a := Int.toNat_of_nonneg h0
      omega
    rw [Nat.mod_eq_of_lt hlt]
    exact Int.toNat_of_nonneg h0
  simp only [ofPackedBytes, hl, if_true, hn, ofBits_toBits]

/-! ### Canonical type names -/

/-- Canonical type names (as selectors spell them): the aliases are spelled
out, and `N = 0` keeps its `x0` (P4). -/
example : FxTy.fixed.name = "fixed128x18" ∧ FxTy.ufixed.name = "ufixed128x18" ∧
    fixed8x1.name = "fixed8x1" ∧ (⟨false, 256, 0, by decide⟩ : FxTy).name = "ufixed256x0" := by
  decide +kernel

/-- `-1.0` at `fixed8x1` is the all-ones word; the word `0xff` (no sign
extension) is rejected by v2 and cleaned to `-0.1` by v1; at `ufixed8x2`,
`2.55` is the word `255` and `256` is rejected. -/
example : (encode (⟨-10, by decide⟩ : Fx fixed8x1)).val = 2 ^ 256 - 10 ∧
    (decodeV2 fixed8x1 ⟨255, by decide⟩).isNone ∧
    (decodeV1 fixed8x1 ⟨255, by decide⟩).1 = -1 ∧
    (encode (⟨255, by decide⟩ : Fx ufixed8x2)).val = 255 ∧
    (decodeV2 ufixed8x2 ⟨256, by decide⟩).isNone := by
  decide +kernel

end Fx

/-! ### Axiom pins -/

/--
info: 'Solidity.Language.FixedPoint.Fx.decodeV2_eq_none_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.decodeV2_eq_none_iff

/--
info: 'Solidity.Language.FixedPoint.Fx.decodeV2_isSome_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.decodeV2_isSome_iff

/--
info: 'Solidity.Language.FixedPoint.Fx.abiEncode_of_abiDecodeV2' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.abiEncode_of_abiDecodeV2

/--
info: 'Solidity.Language.FixedPoint.Fx.ofPackedBytes_encodePacked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.ofPackedBytes_encodePacked

end Solidity.Language.FixedPoint
