import Solidity.Semantics.State
import Solidity.RevertBytes

/-!
# Intrinsic scalar-frame byte images for try producer witnesses

Pure side witnesses, not EVM instructions or source admission. Only scalar
contexts are supported: no live typed memory object is silently overwritten.
The existing typed state remains a field; its heap is not reindexed by bytes.
Capacity is a representation witness, never a gas/fuel/target restriction.
-/
namespace Solidity.Evm.TryByteImage

abbrev U256 := PrimTy.uint.Denote

/-- Retained compiler identity, not an execution semantics. -/
inductive Pipeline where
  | legacy | viaIR
  deriving DecidableEq, Repr

/-- Siblings remain distinct even at equal call depth. -/
structure FrameKey where
  invocation : Nat
  depth : Nat
  pipeline : Pipeline
  declaration : Nat
  self : U256
  sender : U256
  value : U256

/-- Only actual scalar locals are in scope; unreachable caller heap objects
are not incoming physical callee roots. -/
def ScalarFrame (Γ : Ctx) : Prop := ∀ R, Idx Γ (.mem R) → False

/-- A word access has a natural (not modular) end. -/
structure WordSpan (capacity : Nat) where
  offset : U256
  fits : offset.val.toNat + 32 ≤ capacity

/-- An empty slice does not access or validate its offset. -/
structure ByteSpan (capacity : Nat) where
  offset : U256
  length : U256
  fits : length.val.toNat = 0 ∨ offset.val.toNat + length.val.toNat ≤ capacity

/-- Bounded bytes beside an existing intrinsic state. Resident words record
actual access separately from the available representation capacity. -/
structure FrameMem (C : Contract) (Γ : Ctx) where
  st : State C Γ
  key : FrameKey
  scalar : ScalarFrame Γ
  capacity : Nat
  aligned : ∃ k, capacity = k * 32
  data : Fin capacity → UInt8
  highWaterWords : Nat
  resident : highWaterWords * 32 ≤ capacity
  zeroAbove : ∀ i, highWaterWords * 32 ≤ i.val → data i = 0

/-- Big-endian byte of an actual typed uint word. -/
def wordByte (w : U256) (j : Nat) : UInt8 :=
  UInt8.ofNat (w.val.toNat / 256 ^ (31 - j) % 256)

/-- Unaligned byte store, preserving the entire logical state and key. -/
def store32 (μ : FrameMem C Γ) (a : WordSpan μ.capacity) (w : U256) : FrameMem C Γ :=
  { μ with
    data := fun i => if a.offset.val.toNat ≤ i.val ∧ i.val < a.offset.val.toNat + 32
      then wordByte w (i.val - a.offset.val.toNat) else μ.data i
    highWaterWords := max μ.highWaterWords ((a.offset.val.toNat + 32 + 31) / 32)
    resident := by
      rcases μ.aligned with ⟨k, hk⟩
      have ha := a.fits
      have hr := μ.resident
      omega
    zeroAbove := by
      intro i hi
      have hprev := μ.zeroAbove i
      have hw : ¬ (a.offset.val.toNat ≤ i.val ∧ i.val < a.offset.val.toNat + 32) := by
        omega
      rw [if_neg hw]
      apply hprev
      omega }

/-- Extra representation capacity is zero-filled; resident words do not grow
merely because a larger witness was reserved. This is not a gas theorem. -/
def expandZero (μ : FrameMem C Γ) (extraWords : Nat) : FrameMem C Γ :=
  { μ with
    capacity := μ.capacity + extraWords * 32
    aligned := by rcases μ.aligned with ⟨k, hk⟩; exact ⟨k + extraWords, by omega⟩
    data := fun i => if h : i.val < μ.capacity then μ.data ⟨i.val, h⟩ else 0
    resident := by have hr := μ.resident; omega
    zeroAbove := by
      intro i hi
      split
      · exact μ.zeroAbove _ hi
      · rfl }

/-- Expanding reserved capacity preserves every old resident byte. -/
theorem expandZero_old (μ : FrameMem C Γ) (n : Nat) (i : Fin μ.capacity) :
    (expandZero μ n).data ⟨i.val, by change i.val < μ.capacity + n * 32; omega⟩ = μ.data i := dif_pos i.isLt

/-- Newly reserved cells are zero, not unconstrained physical bytes. -/
theorem expandZero_new (μ : FrameMem C Γ) (n : Nat)
    (i : Fin (μ.capacity + n * 32)) (h : μ.capacity ≤ i.val) :
    (expandZero μ n).data i = 0 := dif_neg (by omega)

/-- Immutable snapshot in increasing byte-address order. A ghost observation;
it does not itself simulate REVERT gas or expand resident memory. -/
def snapshot (μ : FrameMem C Γ) (s : ByteSpan μ.capacity) : List UInt8 :=
  List.ofFn fun i : Fin s.length.val.toNat =>
    μ.data ⟨s.offset.val.toNat + i.val, by rcases s.fits with h | h <;> omega⟩

/-- No logical state component or invocation identity changes. -/
theorem store32_frame (μ : FrameMem C Γ) (a : WordSpan μ.capacity) (w : U256) :
    (store32 μ a w).st = μ.st ∧ (store32 μ a w).key = μ.key := ⟨rfl, rfl⟩

/-- Exactly the selected unaligned interval receives word bytes. -/
theorem store32_at (μ : FrameMem C Γ) (a : WordSpan μ.capacity) (w : U256)
    (i : Fin μ.capacity) (h : a.offset.val.toNat ≤ i.val ∧ i.val < a.offset.val.toNat + 32) :
    (store32 μ a w).data i = wordByte w (i.val - a.offset.val.toNat) := if_pos h

/-- Other cells are unchanged. -/
theorem store32_outside (μ : FrameMem C Γ) (a : WordSpan μ.capacity) (w : U256)
    (i : Fin μ.capacity) (h : ¬ (a.offset.val.toNat ≤ i.val ∧ i.val < a.offset.val.toNat + 32)) :
    (store32 μ a w).data i = μ.data i := if_neg h

/-- On overlap, the last writer supplies the byte. -/
theorem overlap_last (μ : FrameMem C Γ) (a b : WordSpan μ.capacity) (v w : U256)
    (i : Fin μ.capacity) (hb : b.offset.val.toNat ≤ i.val ∧ i.val < b.offset.val.toNat + 32) :
    (store32 (store32 μ a v) b w).data i = wordByte w (i.val - b.offset.val.toNat) :=
  store32_at (store32 μ a v) b w i hb

/-- Requested slice length, including empty slices. -/
theorem snapshot_length (μ : FrameMem C Γ) (s : ByteSpan μ.capacity) :
    (snapshot μ s).length = s.length.val.toNat := List.length_ofFn

/-- Indexed reads follow exactly the supplied byte order. -/
theorem snapshot_get (μ : FrameMem C Γ) (s : ByteSpan μ.capacity)
    (i : Nat) (hi : i < (snapshot μ s).length) :
    (snapshot μ s)[i] = μ.data ⟨s.offset.val.toNat + i, by
      have hn := snapshot_length μ s
      rcases s.fits with h | h <;> omega⟩ := List.getElem_ofFn hi

/-- No address check or read is performed by the empty slice. -/
theorem snapshot_empty (μ : FrameMem C Γ) (s : ByteSpan μ.capacity)
    (h : s.length.val.toNat = 0) : snapshot μ s = [] := by
  apply List.eq_nil_of_length_eq_zero
  exact (snapshot_length μ s).trans h

end Solidity.Evm.TryByteImage
