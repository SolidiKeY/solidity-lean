import Solidity.Evm.TryByteImage
import SolidityBridge.RoadmapV15.EncodingUniqueness

/-!
Pure consumers of the published scalar-frame image. Capacity and natural access
bounds are explicit. No physical allocator, opcode execution, gas, source-profile
restriction or Osaka driver is supplied by these equations.
-/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Backend Solidity.Evm.TryByteImage

/-- Byte position in the actual backend encoder, with no input range premise:
width truncates high bytes, and position zero is the most significant byte. -/
theorem backend_byte_at (width value j : Nat) (hj : j < width) :
    (toBytesBE width value)[j] =
      UInt8.ofNat (value / 256 ^ (width - 1 - j) % 256) := by
  induction width generalizing value with
  | zero => omega
  | succ n ih =>
    by_cases h : j < n
    · rw [toBytesBE, Vector.getElem_push_lt h, ih (value / 256) h]
      have he : n + 1 - 1 - j = (n - 1 - j) + 1 := by omega
      rw [Nat.div_div_eq_div_mul, he, Nat.pow_succ, Nat.mul_comm 256]
    · have he : j = n := by omega
      subst j
      simp only [toBytesBE, Vector.getElem_push_eq, Nat.add_sub_cancel,
        Nat.sub_self, Nat.pow_zero, Nat.div_one]

/-- Published image word bytes and the existing backend encoding agree at every
one of the 32 ordered positions. Out-of-word positions are intentionally absent. -/
theorem image_wordByte_backend (w : PrimTy.uint.Denote) (j : Nat) (hj : j < 32) :
    wordByte w j = (toBytesBE 32 w.val.toNat)[j] :=
  (backend_byte_at 32 w.val.toNat j hj).symm

/-- The exact 32-byte observation of a word access, with the same natural bound. -/
def wordObservation (a : WordSpan capacity) : ByteSpan capacity :=
  ⟨a.offset, ⟨32, by decide⟩, Or.inr a.fits⟩

/-- Full ordered bytes at arbitrary (including unaligned) offsets. This consumes
store32_at and snapshot_get, rather than defining a second byte memory. -/
theorem image_store_backend (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (w : PrimTy.uint.Denote) :
    snapshot (store32 μ a w) (wordObservation a) =
      (toBytesBE 32 w.val.toNat).toList := by
  apply List.ext_getElem
  · rw [snapshot_length, Vector.length_toList]; rfl
  · intro i hi hi'
    rw [snapshot_get]
    have hp : a.offset.val.toNat ≤ a.offset.val.toNat + i ∧
        a.offset.val.toNat + i < a.offset.val.toNat + 32 := by
      have hlen : i < 32 := by simpa only [Vector.length_toList] using hi'
      omega
    rw [store32_at μ a w _ hp]
    simp only [wordObservation, Nat.add_sub_cancel_left, Vector.getElem_toList]
    exact image_wordByte_backend w i (by simpa only [Vector.length_toList] using hi')

/-- Complete intrinsic state and full invocation identity accompany exact bytes.
ScalarFrame is a field of this producer's image, not an admission rule. -/
theorem image_store_observation (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (w : PrimTy.uint.Denote) :
    (store32 μ a w).st = μ.st ∧ (store32 μ a w).key = μ.key ∧
    snapshot (store32 μ a w) (wordObservation a) =
      (toBytesBE 32 w.val.toNat).toList :=
  ⟨(store32_frame μ a w).1, (store32_frame μ a w).2, image_store_backend μ a w⟩

/-- Surrounding bytes are preserved pointwise, with the natural interval explicit. -/
theorem image_store_surrounding (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (w : PrimTy.uint.Denote) (i : Fin μ.capacity)
    (outside : i.val < a.offset.val.toNat ∨ a.offset.val.toNat + 32 ≤ i.val) :
    (store32 μ a w).data i = μ.data i :=
  store32_outside μ a w i (by omega)

/-- Reference-image readback through the actual backend reader, without padding
or allocator hypotheses. The intrinsic word already carries the full-word bound. -/
theorem image_store_read (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (w : PrimTy.uint.Denote) :
    ofBytesBE (snapshot (store32 μ a w) (wordObservation a)) = w.val.toNat := by
  rw [image_store_backend]
  have h : w.val.toNat < 256 ^ 32 := by
    have hu := (Scalar.encodeValue .uint w).isLt
    rw [Scalar.encode_uint_toNat] at hu
    exact hu
  exact ofBytesBE_toBytesBE 32 w.val.toNat h

/-- All intrinsic scalar encodings, including signed two's complement, transport
through the existing toWord representation; no alternate signedness is defined. -/
theorem image_store_typed (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (p : PrimTy) (v : p.Denote) :
    snapshot (store32 μ a (PrimTy.toWord v)) (wordObservation a) =
      (toBytesBE 32 (Scalar.encodeValue p v).toNat).toList := by
  rw [image_store_backend, typed_bytes_toWord]

theorem image_store_signed (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (v : PrimTy.int.Denote) :
    (Scalar.immediate (snapshot (store32 μ a (PrimTy.toWord v))
      (wordObservation a))).toInt = v.val := by
  rw [image_store_typed μ a .int v, signed_word_bytes]

/-- Last writer observation retains exact order, even when the first access
partially overlaps the second. No disjointness premise is needed. -/
theorem image_overlap_backend (μ : FrameMem C Γ) (a b : WordSpan μ.capacity)
    (v w : PrimTy.uint.Denote) :
    snapshot (store32 (store32 μ a v) b w) (wordObservation b) =
      (toBytesBE 32 w.val.toNat).toList := image_store_backend (store32 μ a v) b w

/-- Disjoint later writes frame the complete earlier word observation. -/
theorem image_disjoint_backend (μ : FrameMem C Γ) (a b : WordSpan μ.capacity)
    (v w : PrimTy.uint.Denote)
    (apart : a.offset.val.toNat + 32 ≤ b.offset.val.toNat ∨
      b.offset.val.toNat + 32 ≤ a.offset.val.toNat) :
    snapshot (store32 (store32 μ a v) b w) (wordObservation a) =
      (toBytesBE 32 v.val.toNat).toList := by
  rw [← image_store_backend μ a v]
  apply List.ext_getElem
  · rw [snapshot_length, snapshot_length]
  · intro i hi hi'
    rw [snapshot_get, snapshot_get]
    apply image_store_surrounding
    have hlen : i < 32 := by simpa only [snapshot_length, wordObservation] using hi
    change a.offset.val.toNat + i < b.offset.val.toNat ∨
      b.offset.val.toNat + 32 ≤ a.offset.val.toNat + i
    omega

/-- Reuse the intrinsic uint range for a backend word. This is representation
transport only; the BitVec input already contains exactly the modulo-2^256 value. -/
def imageScalarWord (w : Scalar.Word) : PrimTy.uint.Denote :=
  ⟨Int.ofNat w.toNat, by
    have h : w.toNat < 2 ^ 256 := w.isLt
    simp only [PrimTy.inRange, decide_eq_true_eq, Int.ofNat_eq_natCast]
    exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr h⟩⟩

/-- Exact full scalar-word bytes, including already-truncated BitVec inputs. -/
theorem image_store_scalar (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (w : Scalar.Word) :
    snapshot (store32 μ a (imageScalarWord w)) (wordObservation a) =
      (toBytesBE 32 w.toNat).toList := image_store_backend μ a _

/-- Arbitrary natural input uses the actual backend word modulo, with all 32
bytes retained. No modular address addition is inferred. -/
theorem image_store_modulo (μ : FrameMem C Γ) (a : WordSpan μ.capacity) (n : Nat) :
    snapshot (store32 μ a (imageScalarWord (BitVec.ofNat 256 n))) (wordObservation a) =
      (toBytesBE 32 (n % 2 ^ 256)).toList := by
  rw [image_store_scalar, BitVec.toNat_ofNat]

/-- Existing unsigned cleanup observed through complete byte images. This is the
published local scalar runner, not physical MSTORE or an Osaka step theorem. -/
theorem image_unsigned_cleanup (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (width : Fin 32) (w : Scalar.Word) (tail : Scalar.Stack) :
    Scalar.run (Scalar.unsignedCode width)
      (Scalar.immediate (snapshot (store32 μ a (imageScalarWord w))
        (wordObservation a)) :: tail) =
      some (Scalar.immediate (snapshot (store32 μ a
        (imageScalarWord (Scalar.unsignedClean width w))) (wordObservation a)) :: tail) := by
  rw [image_store_scalar, image_store_scalar]
  exact unsigned_cleanup_bytes width w tail

theorem image_signed_cleanup (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (width : Fin 32) (w : Scalar.Word) (tail : Scalar.Stack) :
    Scalar.run (Scalar.signedCode width)
      (Scalar.immediate (snapshot (store32 μ a (imageScalarWord w))
        (wordObservation a)) :: tail) =
      some (Scalar.immediate (snapshot (store32 μ a
        (imageScalarWord (Scalar.signedClean width w))) (wordObservation a)) :: tail) := by
  rw [image_store_scalar, image_store_scalar]
  exact signed_cleanup_bytes width w tail

end SolidityBridge.RoadmapV15
