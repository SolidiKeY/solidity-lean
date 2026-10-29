import Solidity.Source.State

/-!
# Source values and observations (S04.02)

What a source execution shows at the transaction boundary, independently
of the compiler, under the approved interpretations (G01 Q5: the full
revert bytes, `Panic` codes included; opaque hashes are the fixed
Keccak-256, `Solidity.Roadmap.keccakWord`):

- `Val.word`: the ABI word of a value-type value (two's complement for
  signed integers and fixed-point values, left-aligned `bytesN`, addresses
  and enum positions right-aligned), with `Val.word_int` reading an integer
  back;
- `wordBytes`: a word as its 32 big-endian bytes (`wordBytes_length`,
  `wordBytes_value`);
- `selector`: the first four bytes of the Keccak-256 of a signature;
- `PanicCode` and `panicData`: `Panic(uint256)` with solc's codes;
  `errorData`: `Error(string)`;
- `revertOutcome`: the `Outcome` (G01's shared observation) of a revert
  with those bytes.

Environment observations (`msg.sender`, `msg.value`, `block.timestamp`,
`this`, balances) are the session environment's (G01 `SessionEnv`,
`Request`): a source semantics reads them, it does not choose them.
-/

namespace Solidity.Source

open Solidity.Roadmap (Address Word Bytes Outcome keccakWord)

/-- A natural number below `2^256` as a word. -/
def toWord (n : Nat) : Word := ⟨n % 2 ^ 256, Nat.mod_lt _ (by decide)⟩

/-- An integer as a two's-complement word. -/
def intWord (v : Int) : Word := toWord (v % (2 ^ 256 : Nat)).toNat

/-- The big-endian bytes of a number, `k` of them. -/
def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => beBytes k (n / 256) ++ [UInt8.ofNat (n % 256)]

/-- A word as its 32 big-endian bytes. -/
def wordBytes (w : Word) : Bytes := beBytes 32 w.val

/-- The number big-endian bytes denote. -/
def beValue (bs : List UInt8) : Nat := bs.foldl (fun acc b => acc * 256 + b.toNat) 0

theorem beBytes_length (k n : Nat) : (beBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [beBytes, List.length_append, ih, List.length_singleton]

theorem wordBytes_length (w : Word) : (wordBytes w).length = 32 := beBytes_length 32 w.val

theorem beValue_append (bs : List UInt8) (b : UInt8) : beValue (bs ++ [b]) = beValue bs * 256 + b.toNat := by
  simp only [beValue, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem beValue_beBytes (k n : Nat) (h : n < 256 ^ k) : beValue (beBytes k n) = n := by
  induction k generalizing n with
  | zero =>
    simp only [Nat.pow_zero] at h
    have : n = 0 := by omega
    subst this; rfl
  | succ k ih =>
    simp only [beBytes, beValue_append]
    have hq : n / 256 < 256 ^ k := by
      rw [Nat.pow_succ] at h
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    rw [ih _ hq]
    have hm : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
      simp only [UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
      omega
    rw [hm]
    omega

/-- **A word's bytes denote the word.** -/
theorem wordBytes_value (w : Word) : beValue (wordBytes w) = w.val :=
  beValue_beBytes 32 w.val (by have := w.isLt; simpa using this)

/-- The ABI word of a value-type value; `none` for references and function
values. -/
def Val.word {D : Layout} {τ : STy} : Val D τ → Option Word
  | .int v _ => some (intWord v)
  | .bool b => some (toWord (if b then 1 else 0))
  | .address a => some (toWord a.val)
  | .fixedBytes bs _ => some (toWord (beValue (bs ++ List.replicate (32 - bs.length) 0)))
  | .fixed v _ => some (intWord v)
  | .enum i => some (toWord i.val)
  | .udvt v => v.word
  | .contract a => some (toWord a.val)
  | _ => none

/-- The integer a word encodes at a type, two's complement for a signed
one. -/
def wordInt (t : IntTy) (w : Word) : Int :=
  if t.signed ∧ 2 ^ 255 ≤ w.val then (w.val : Int) - 2 ^ 256 else w.val

/-- **Decoding a word at an integer type**: `none` for a word that is not
the sign or zero extension of a value in range (the ABI decoder reverts on
it). -/
def readInt (t : IntTy) (w : Word) : Option Int :=
  let v := wordInt t w
  if t.lo ≤ v ∧ v ≤ t.hi then some v else none

/-- **The ABI word of an integer decodes to the integer.** -/
theorem Val.word_int {D : Layout} {t : IntTy} (v : Int) (h : t.lo ≤ v ∧ v ≤ t.hi) :
    (Val.int (D := D) (t := t) v h).word.bind (readInt t) = some v := by
  have hw : wordInt t (intWord v) = v := by
    obtain ⟨s, b, hb⟩ := t
    have hb1 : 2 ^ (b - 1) ≤ 2 ^ 255 := Nat.pow_le_pow_right (by decide) (by omega)
    have hb2 : 2 ^ b ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by omega)
    simp only [IntTy.lo, IntTy.hi] at h
    simp only [wordInt, intWord, toWord]
    cases s
    · simp only [Bool.false_eq_true, if_false, false_and] at h ⊢
      simp only [Nat.reducePow] at hb2 ⊢
      omega
    · simp only [if_true, true_and] at h ⊢
      simp only [Nat.reducePow] at hb1 ⊢
      split <;> omega
  simp only [Val.word, Option.bind_some, readInt, hw, h, and_self, if_true]

/-- A word out of a type's range does not decode: `300` at `uint8`. -/
theorem readInt_reject : readInt IntTy.u8 (toWord 300) = none := by decide

/-! ## Selectors and revert data -/

/-- The selector of a signature: the first four bytes of its Keccak-256. -/
def selector (sig : String) : Bytes := (wordBytes (keccakWord sig.toUTF8.toList)).take 4

theorem selector_length (sig : String) : (selector sig).length = 4 := by
  simp only [selector, List.length_take, wordBytes_length]
  rfl

/-- `Panic(uint256)`'s selector, `0x4e487b71` (checked against Keccak-256
by `#guard` below). -/
def panicSelector : Bytes := [0x4e, 0x48, 0x7b, 0x71]

/-- `Error(string)`'s selector, `0x08c379a0`. -/
def errorSelector : Bytes := [0x08, 0xc3, 0x79, 0xa0]

/-- solc's panic codes. -/
inductive PanicCode where
  | generic | assert | arithmetic | divZero | enumConv | storageEncoding | popEmpty | index
  | alloc | zeroFn
  deriving DecidableEq, Repr

/-- The code's number. -/
def PanicCode.code : PanicCode → Nat
  | .generic => 0x00
  | .assert => 0x01
  | .arithmetic => 0x11
  | .divZero => 0x12
  | .enumConv => 0x21
  | .storageEncoding => 0x22
  | .popEmpty => 0x31
  | .index => 0x32
  | .alloc => 0x41
  | .zeroFn => 0x51

/-- The codes are distinct. -/
theorem PanicCode.code_injective {a b : PanicCode} (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp only [PanicCode.code] at h; omega)

/-- `Panic(c)`'s revert data: the selector and the code as a word. -/
def panicData (c : PanicCode) : Bytes := panicSelector ++ wordBytes (toWord c.code)

theorem panicData_length (c : PanicCode) : (panicData c).length = 36 := by
  simp only [panicData, List.length_append, wordBytes_length]
  rfl

/-- **The code reads back from the data.** -/
theorem panicData_code (c : PanicCode) : beValue ((panicData c).drop 4) = c.code := by
  have hc : c.code < 2 ^ 256 := by cases c <;> decide
  simp only [panicData, panicSelector, List.cons_append, List.nil_append, List.drop_succ_cons,
    List.drop_zero, wordBytes_value, toWord, Nat.mod_eq_of_lt hc]

/-- Bytes padded with zeros to a multiple of 32. -/
def pad32 (bs : Bytes) : Bytes := bs ++ List.replicate ((32 - bs.length % 32) % 32) 0

/-- `Error(msg)`'s revert data: the selector, the offset `32`, the length,
and the bytes padded (the ABI encoding of one `string`). -/
def errorData (msg : Bytes) : Bytes :=
  errorSelector ++ wordBytes (toWord 32) ++ wordBytes (toWord msg.length) ++ pad32 msg

theorem errorData_prefix (msg : Bytes) : (errorData msg).take 4 = errorSelector := by
  simp only [errorData, errorSelector, List.append_assoc, List.cons_append, List.nil_append,
    List.take_succ_cons, List.take_zero]

/-- A source revert's outcome: its data, verbatim (G01 Q5). -/
def revertOutcome (data : Bytes) : Outcome := .revert data

/-- A failed `assert` and an arithmetic overflow are distinct outcomes. -/
theorem panic_distinct {a b : PanicCode} (h : revertOutcome (panicData a) = revertOutcome (panicData b)) :
    a = b := by
  simp only [revertOutcome, Outcome.revert.injEq] at h
  have := congrArg (fun bs => beValue (bs.drop 4)) h
  simp only [panicData_code] at this
  exact PanicCode.code_injective this

end Solidity.Source

/-! The hard-coded selectors are the Keccak-256 ones (evaluated, not proved). -/
#guard Solidity.Source.selector "Panic(uint256)" == Solidity.Source.panicSelector
#guard Solidity.Source.selector "Error(string)" == Solidity.Source.errorSelector
