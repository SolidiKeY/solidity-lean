import Solidity.Roadmap.Contracts

/-!
# Physical byte operations

This is a view, not a second source state. Addresses are natural byte offsets;
`ValidRange` is required by future successful EVM steps (overflow/allocation
failure is not silently wrapped). Copies read a snapshot, including overlaps.
No allocation, gas, or memory size observation is defined here.
-/
namespace Solidity.Yul.Views

abbrev ByteView := Nat → UInt8

/-- A non-wrapping EVM byte interval; empty intervals do not access memory. -/
def ValidRange (a n : Nat) : Prop := n = 0 ∨ a + n ≤ 2 ^ 256

def saveByte (m : ByteView) (a : Nat) (v : UInt8) : ByteView :=
  fun b => if b = a then v else m b

theorem find_saveByte (m : ByteView) (a : Nat) (v : UInt8) :
    saveByte m a v a = v := by simp only [saveByte, ↓reduceIte]

theorem find_saveByte_other (m : ByteView) {a b : Nat} (v : UInt8) (h : b ≠ a) :
    saveByte m a v b = m b := by simp only [saveByte, if_neg h]

/-- Snapshot copy: the right-hand side always reads the original `src`. -/
def copyBytes (dst src : ByteView) (to start n : Nat) : ByteView :=
  fun a => if to ≤ a ∧ a < to + n then src (start + (a - to)) else dst a

def mcopy (m : ByteView) (to start n : Nat) : ByteView := copyBytes m m to start n

theorem find_copyBytes (dst src : ByteView) (to start n i : Nat) (hi : i < n) :
    copyBytes dst src to start n (to + i) = src (start + i) := by
  simp only [copyBytes, Nat.le_add_right, Nat.add_lt_add_iff_left, hi,
    and_self, if_true, Nat.add_sub_cancel_left]

theorem copyBytes_outside (dst src : ByteView) (to start n a : Nat)
    (h : ¬ (to ≤ a ∧ a < to + n)) : copyBytes dst src to start n a = dst a := by
  simp only [copyBytes, if_neg h]

theorem copyBytes_zero (dst src : ByteView) (to start : Nat) :
    copyBytes dst src to start 0 = dst := by
  funext a
  have h : ¬ (to ≤ a ∧ a < to + 0) := by omega
  exact copyBytes_outside dst src to start 0 a h

theorem mcopy_self (m : ByteView) (a n : Nat) : mcopy m a a n = m := by
  funext b
  unfold mcopy copyBytes
  split
  · rename_i h
    rw [Nat.add_sub_of_le h.1]
  · rfl

/-- Big-endian word bytes: byte zero is most significant. -/
def wordByte (w : Roadmap.Word) (i : Fin 32) : UInt8 :=
  UInt8.ofNat (w.val / 256 ^ (31 - i.val))

/-- Mathematical big-endian read, exactly 32 bytes. -/
def readBE (m : ByteView) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 256 * readBE m a n + (m (a + n)).toNat

def mloadNat (m : ByteView) (a : Nat) : Nat := readBE m a 32

def mstore (m : ByteView) (a : Nat) (w : Roadmap.Word) : ByteView :=
  fun b => if h : a ≤ b ∧ b < a + 32 then wordByte w ⟨b - a, by omega⟩ else m b

def mstore8 (m : ByteView) (a : Nat) (w : Roadmap.Word) : ByteView :=
  saveByte m a (UInt8.ofNat w.val)

theorem find_mstore (m : ByteView) (a : Nat) (w : Roadmap.Word) (i : Fin 32) :
    mstore m a w (a + i.val) = wordByte w i := by
  simp only [mstore, Nat.le_add_right, Nat.add_lt_add_iff_left, i.isLt,
    and_self, ↓reduceDIte, Nat.add_sub_cancel_left]

theorem mstore_outside (m : ByteView) (a b : Nat) (w : Roadmap.Word)
    (h : ¬ (a ≤ b ∧ b < a + 32)) : mstore m a w b = m b := by
  simp only [mstore, dif_neg h]

/-- `mload` as bytes, useful before the numeric word codec is composed. -/
def readBytes (m : ByteView) (a n : Nat) : List UInt8 :=
  (List.range n).map fun i => m (a + i)

end Solidity.Yul.Views
