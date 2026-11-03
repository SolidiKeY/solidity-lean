import Solidity.Evm.TryPanicSourceControl

/-! Generic byte projection of the SAME bounded H8 image. The sparse bytes
below are derived from the original word operands and prologue, not an expected
observation. No allocation, padding, source lowering or EVM outcome is assumed. -/
namespace Solidity.Evm.TryPanicSourceBytes
open TryByteImage TryPanicProducer TryPanicSourcePlan TryPanicSourceFrame
variable {C : Contract}

/-- Nonzero positions of the final image, including the live prologue byte. -/
def byteAt (i : Nat) : UInt8 :=
  if i = 0 then 0x4e else if i = 1 then 0x48 else
  if i = 2 then 0x7b else if i = 3 then 0x71 else
  if i = 35 then 0x43 else if i = 95 then 0x80 else 0

theorem selector_byte : ∀ i : Fin 32,
    wordByte selectorWord i.val =
      (if i.val = 0 then 0x4e else if i.val = 1 then 0x48 else
       if i.val = 2 then 0x7b else if i.val = 3 then 0x71 else 0) := by decide

theorem code_byte : ∀ i : Fin 32,
    wordByte codeWord i.val = (if i.val = 31 then 0x43 else 0) := by decide

theorem free_byte : ∀ i : Fin 32,
    wordByte freeWord i.val = (if i.val = 31 then 0x80 else 0) := by decide

/-- Actual store order, before any byte arithmetic normalization. -/
theorem image_expression (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) (i : Fin K) :
    (imageK σ key K aligned large).data i =
      if 4 ≤ i.val ∧ i.val < 36 then wordByte codeWord (i.val - 4) else
      if 0 ≤ i.val ∧ i.val < 32 then wordByte selectorWord i.val else
      if 64 ≤ i.val ∧ i.val < 96 then wordByte freeWord (i.val - 64) else 0 := rfl

/-- Overlapping source stores and retained prologue reduce to this exact
byte function for ALL indices/capacities, without a universal word-size cast. -/
theorem image_byte (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) (i : Fin K) :
    (imageK σ key K aligned large).data i = byteAt i.val := by
  rw [image_expression]
  by_cases hc : 4 ≤ i.val ∧ i.val < 36
  · rw [if_pos hc, code_byte ⟨i.val - 4, by omega⟩]
    have last : i.val - 4 = 31 ↔ i.val = 35 := by omega
    simp only [byteAt, if_neg (by omega : i.val ≠ 0), if_neg (by omega : i.val ≠ 1),
      if_neg (by omega : i.val ≠ 2), if_neg (by omega : i.val ≠ 3),
      if_neg (by omega : i.val ≠ 95), last]
  · rw [if_neg hc]
    by_cases hs : 0 ≤ i.val ∧ i.val < 32
    · rw [if_pos hs, selector_byte ⟨i.val, hs.2⟩]
      simp only [byteAt, if_neg (by omega : i.val ≠ 35), if_neg (by omega : i.val ≠ 95)]
    · rw [if_neg hs]
      by_cases hf : 64 ≤ i.val ∧ i.val < 96
      · rw [if_pos hf, free_byte ⟨i.val - 64, by omega⟩]
        have last : i.val - 64 = 31 ↔ i.val = 95 := by omega
        simp only [byteAt, if_neg (by omega : i.val ≠ 0), if_neg (by omega : i.val ≠ 1),
          if_neg (by omega : i.val ≠ 2), if_neg (by omega : i.val ≠ 3),
          if_neg (by omega : i.val ≠ 35), last]
      · rw [if_neg hf]
        simp only [byteAt, if_neg (by omega : i.val ≠ 0), if_neg (by omega : i.val ≠ 1),
          if_neg (by omega : i.val ≠ 2), if_neg (by omega : i.val ≠ 3),
          if_neg (by omega : i.val ≠ 35), if_neg (by omega : i.val ≠ 95)]

/-- Byte projection for the actual natural local length. No truncation to36. -/
def bytesAt (n : Nat) : List UInt8 := List.ofFn fun i : Fin n => byteAt i.val

theorem bytes_length (n : Nat) : (bytesAt n).length = n := List.length_ofFn

/-- Every finite-capacity image produces the SAME generic local-length bytes.
This removes K/key/final-image choices from the remaining body producer goal. -/
theorem data_eq (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K)
    (fits : (TEnv.get sizeSlot σ.env).val.toNat ≤ K) :
    dataK σ key K aligned large fits = bytesAt (TEnv.get sizeSlot σ.env).val.toNat := by
  apply List.ext_getElem
  · rw [data_length, bytes_length]
  · intro i hi hj
    rw [data_get σ key K aligned large fits i hi, image_byte]
    simp only [bytesAt, List.getElem_ofFn]

/-- Exact equivalent, simplified operational body obligation. This theorem
supplies the byte calculation, NOT the missing intrinsic program execution. -/
theorem realizes_iff (body : Prog C Input Input) :
    TryPanicSourceControl.BodyRealizes body ↔
      ∀ σ : State C Input, body.runR σ =
        .error (THalt.ofData (bytesAt (TEnv.get sizeSlot σ.env).val.toNat)) := by
  constructor
  · intro realizes σ
    let n : Nat := (TEnv.get sizeSlot σ.env).val.toNat
    have large : 96 ≤ (n + 3) * 32 := by omega
    have fits : (TEnv.get sizeSlot σ.env).val.toNat ≤ (n + 3) * 32 := by
      change n ≤ (n + 3) * 32
      omega
    have run : body.runR σ = .error (THalt.ofData
        (dataK σ (frameKey .legacy 0 0 σ) ((n + 3) * 32) ⟨n + 3, rfl⟩ large fits)) :=
      realizes σ (frameKey .legacy 0 0 σ) ((n + 3) * 32) ⟨n + 3, rfl⟩ large fits
    rw [data_eq] at run
    exact run
  · intro run σ key K aligned large fits
    rw [data_eq]
    exact run σ

/-- Capacity labels do not select the payload, once the actual local range fits. -/
theorem data_independent (σ : State C Input) (a b : FrameKey) (K L : Nat)
    (ka : ∃ k, K = k*32) (la : ∃ k, L = k*32) (kb : 96 ≤ K) (lb : 96 ≤ L)
    (kf : (TEnv.get sizeSlot σ.env).val.toNat ≤ K)
    (lf : (TEnv.get sizeSlot σ.env).val.toNat ≤ L) :
    dataK σ a K ka kb kf = dataK σ b L la lb lf := by
  rw [data_eq, data_eq]

/-- Truncation keeps exactly the requested source length; long output still
exposes the modeled prologue rather than silently becoming canonical Panic. -/
theorem empty_bytes : bytesAt 0 = [] := rfl

theorem short_length : (bytesAt 6).length = 6 := bytes_length 6

theorem bytes_get (n i : Nat) (hi : i < (bytesAt n).length) :
    (bytesAt n)[i] = byteAt i := by
  simp only [bytesAt, List.getElem_ofFn]

theorem long_prologue : (bytesAt 256)[95]'(by rw [bytes_length]; decide) = 0x80 := by
  rw [bytes_get]
  rfl

theorem long_zero : (bytesAt 256)[96]'(by rw [bytes_length]; decide) = 0 := by
  rw [bytes_get]
  rfl

theorem mismatch_short : bytesAt 6 ≠ computed36 := by
  intro h
  have lengths : (bytesAt 6).length = computed36.length := congrArg List.length h
  rw [bytes_length, computed36_length] at lengths
  omega

end Solidity.Evm.TryPanicSourceBytes
