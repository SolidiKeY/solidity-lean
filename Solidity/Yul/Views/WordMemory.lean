import Solidity.Yul.Views.Bytes

/-! Exact big-endian word roundtrip and bounded loads. -/
namespace Solidity.Yul.Views

theorem readBE_lt (m : ByteView) (a n : Nat) : readBE m a n < 256 ^ n := by
  induction n with
  | zero => simp only [readBE, Nat.pow_zero]; decide
  | succ n ih =>
    have hb : (m (a + n)).toNat < 256 := UInt8.toNat_lt _
    rw [readBE, Nat.pow_succ]
    omega

def mload (m : ByteView) (a : Nat) : Roadmap.Word :=
  ⟨mloadNat m a, by exact readBE_lt m a 32⟩

private theorem division_byte (x k : Nat) :
    256 * (x / 256 ^ (k + 1)) + x / 256 ^ k % 256 = x / 256 ^ k := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.div_add_mod (x / 256 ^ k) 256

theorem readBE_congr (m m' : ByteView) (a n : Nat)
    (h : ∀ i, i < n → m (a + i) = m' (a + i)) : readBE m a n = readBE m' a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 256 * readBE m a n + (m (a + n)).toNat =
      256 * readBE m' a n + (m' (a + n)).toNat
    rw [ih (fun i hi => h i (by omega)), h n (Nat.lt_succ_self n)]

theorem mload_congr (m m' : ByteView) (a : Nat)
    (h : ∀ i : Fin 32, m (a + i.val) = m' (a + i.val)) : mload m a = mload m' a := by
  apply Fin.ext
  exact readBE_congr m m' a 32 (fun i hi => h ⟨i, hi⟩)

/-- Every written word prefix agrees with its high bytes. -/
theorem readBE_mstore_prefix (m : ByteView) (a : Nat) (w : Roadmap.Word)
    (n : Nat) (hn : n ≤ 32) :
    readBE (mstore m a w) a n = w.val / 256 ^ (32 - n) := by
  induction n with
  | zero =>
    have hw : w.val < 256 ^ 32 := w.isLt
    simp only [readBE, Nat.sub_zero, Nat.div_eq_of_lt hw]
  | succ n ih =>
    have hni : n < 32 := by omega
    have he : 32 - n = (31 - n) + 1 := by omega
    have he' : 32 - (n + 1) = 31 - n := by omega
    rw [readBE, ih (by omega)]
    have hb := find_mstore m a w ⟨n, hni⟩
    change mstore m a w (a + n) = _ at hb
    rw [hb]
    change 256 * (w.val / 256 ^ (32 - n)) +
      (UInt8.ofNat (w.val / 256 ^ (31 - n))).toNat = w.val / 256 ^ (32 - (n + 1))
    rw [UInt8.toNat_ofNat', he, he']
    exact division_byte w.val (31 - n)

/-- Numeric decode-after-encode, no premise about previous memory. -/
theorem mload_mstore (m : ByteView) (a : Nat) (w : Roadmap.Word) :
    mload (mstore m a w) a = w := by
  apply Fin.ext
  change readBE (mstore m a w) a 32 = w.val
  rw [readBE_mstore_prefix m a w 32 (Nat.le_refl _)]
  simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one]

/-- Removing trailing bytes is exact; all bytes are retained in the word view. -/
theorem readBE_div (m : ByteView) (a n k : Nat) (hk : k ≤ n) :
    readBE m a n / 256 ^ k = readBE m a (n - k) := by
  induction k with
  | zero => simp only [Nat.pow_zero, Nat.div_one, Nat.sub_zero]
  | succ k ih =>
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ih (by omega)]
    have he : n - k = (n - (k + 1)) + 1 := by omega
    rw [he, readBE, Nat.add_comm, Nat.add_mul_div_left _ _ (by decide),
      Nat.div_eq_of_lt (UInt8.toNat_lt _), Nat.zero_add]

/-- Every byte of an arbitrary memory window survives load/store unchanged. -/
theorem wordByte_mload (m : ByteView) (a : Nat) (i : Fin 32) :
    wordByte (mload m a) i = m (a + i.val) := by
  change UInt8.ofNat (readBE m a 32 / 256 ^ (31 - i.val)) = m (a + i.val)
  rw [readBE_div m a 32 (31 - i.val) (by omega)]
  have he : 32 - (31 - i.val) = i.val + 1 := by have hi := i.isLt; omega
  rw [he, readBE]
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat']
  change (256 * readBE m a i.val + (m (a + i.val)).toNat) % 256 = _
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (UInt8.toNat_lt _)]

/-- Exact unchanged-view writeback at word granularity, including residual bytes. -/
theorem mstore_mload (m : ByteView) (a : Nat) : mstore m a (mload m a) = m := by
  funext b
  by_cases h : a ≤ b ∧ b < a + 32
  · have hi : b - a < 32 := by omega
    have he : a + (b - a) = b := Nat.add_sub_of_le h.1
    have hb := find_mstore m a (mload m a) ⟨b - a, hi⟩
    rw [he] at hb
    rw [hb, wordByte_mload, he]
  · exact mstore_outside m a b (mload m a) h

end Solidity.Yul.Views
