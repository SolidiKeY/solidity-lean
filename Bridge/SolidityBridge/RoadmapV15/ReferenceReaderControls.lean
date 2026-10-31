import SolidityBridge.RoadmapV15.ReferenceWordObservation

/-! Kernel controls for the actual pinned reader and uint constructor, including
complete ordered bytes, signed/boundary/narrow images. No allocator or execution
witness is constructed. MemoryBytes/driver imports are deliberately unnecessary. -/
namespace SolidityBridge.RoadmapV15.ReferenceReaderControls
open Solidity Solidity.Backend Solidity.Evm.TryByteImage

example : EvmYul.fromBytesBigEndian ([1, 2] : List UInt8) = 258 := by decide +kernel
example : EvmYul.fromBytesBigEndian ([2, 1] : List UInt8) = 513 := by decide +kernel
example : EvmYul.fromBytesBigEndian ([1, 2] : List UInt8) ≠
    EvmYul.fromBytesBigEndian [2, 1] := by decide +kernel
example : EvmYul.fromBytesBigEndian ([0, 1, 2] : List UInt8) =
    EvmYul.fromBytesBigEndian [1, 2] ∧ ([0, 1, 2] : List UInt8) ≠ [1, 2] := by decide +kernel
example : EvmYul.fromBytesBigEndian ([] : List UInt8) =
    EvmYul.fromBytesBigEndian [0] ∧ ([] : List UInt8) ≠ [0] := by decide +kernel
example : EvmYul.fromBytesBigEndian (toBytesBE 2 258).toList = 258 :=
  reference_backend_bounded 2 258 (by decide)
example : ¬ (258 < 256 ^ 1) := by decide
example : EvmYul.fromBytesBigEndian (toBytesBE 1 258).toList ≠ 258 := by decide +kernel
example : (toBytesBE 32 258).toList = List.replicate 30 0 ++ [1, 2] := by decide +kernel
example : (toBytesBE 32 258).toList ≠ (toBytesBE 32 258).toList.reverse := by decide +kernel
example : (toBytesBE 32 258).toList ≠ (toBytesBE 31 258).toList := by decide +kernel
example : (toBytesBE 32 258).toList ≠ (toBytesBE 33 258).toList := by decide +kernel
example : (toBytesBE 32 258).toList ++ (toBytesBE 32 513).toList ≠
    (toBytesBE 32 513).toList ++ (toBytesBE 32 258).toList := by decide +kernel
example : (EvmYul.UInt256.ofNat (EvmYul.fromBytesBigEndian
    (toBytesBE 32 (257 : Scalar.Word).toNat).toList)).toNat = 257 := reference_word_toNat 257
example : (EvmYul.UInt256.ofNat (2 ^ 256 + 513)).toNat = 513 := by decide +kernel
example : (EvmYul.UInt256.ofNat (2 ^ 256 - 1)).toNat ≠ 0 := by decide +kernel

private def C : Contract := { vars := [] }
private def u (n : Nat) (h : n < 2 ^ 256 := by decide) : PrimTy.uint.Denote :=
  ⟨Int.ofNat n, by
    simp only [PrimTy.inRange, decide_eq_true_eq, Int.ofNat_eq_natCast]
    exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr h⟩⟩
private def σ : State C [] :=
  { State.init C with
    net := [(u 7, 9)]
    selfBalance := u 13
    tx := { msgSender := u 11, msgValue := u 13, selfAddress := u 7 } }
private def μ : FrameMem C [] :=
  { st := σ
    key := ⟨29, 2, .legacy, 31, u 7, u 11, u 13⟩
    scalar := by intro R i; cases i
    capacity := 64
    aligned := ⟨2, rfl⟩
    data := fun _ => 0
    highWaterWords := 0
    resident := by decide
    zeroAbove := by intro i _; rfl }
private def a : WordSpan μ.capacity := ⟨u 1, by decide⟩
private def b : WordSpan μ.capacity := ⟨u 2, by decide⟩
private def last : WordSpan μ.capacity := ⟨u 32, by decide⟩
private def negativeOne : PrimTy.int.Denote := ⟨-1, by decide⟩
private def minimumSigned : PrimTy.int.Denote := ⟨-((2 ^ 255 : Nat) : Int), by decide +kernel⟩

example : EvmYul.fromBytesBigEndian (snapshot (store32 μ a (u 258)) (wordObservation a)) = 258 :=
  image_reference_reader μ a (u 258)
example : (EvmYul.UInt256.ofNat (EvmYul.fromBytesBigEndian
    (snapshot (store32 μ a (imageScalarWord 258)) (wordObservation a)))).toNat = 258 :=
  image_reference_word μ a 258
example : (EvmYul.UInt256.ofNat (EvmYul.fromBytesBigEndian
    (snapshot (store32 μ last (imageScalarWord (BitVec.ofNat 256 (2 ^ 256 - 1))))
      (wordObservation last)))).toNat = (BitVec.ofNat 256 (2 ^ 256 - 1)).toNat :=
  image_reference_word μ last _
example : (BitVec.ofNat 256 (EvmYul.fromBytesBigEndian
    (snapshot (store32 μ a (PrimTy.toWord negativeOne)) (wordObservation a)))).toInt = -1 :=
  image_reference_signed μ a negativeOne
example : (BitVec.ofNat 256 (EvmYul.fromBytesBigEndian
    (snapshot (store32 μ a (PrimTy.toWord minimumSigned)) (wordObservation a)))).toInt =
      -((2 ^ 255 : Nat) : Int) := image_reference_signed μ a minimumSigned
example : EvmYul.fromBytesBigEndian
    (snapshot (store32 μ a (imageScalarWord (Scalar.unsignedClean ⟨0, by decide⟩ 257)))
      (wordObservation a)) = 1 := by
  rw [image_store_scalar, reference_big_reader]; decide +kernel
example : (BitVec.ofNat 256 (EvmYul.fromBytesBigEndian
    (snapshot (store32 μ a (imageScalarWord (Scalar.signedClean ⟨0, by decide⟩ 128)))
      (wordObservation a)))).toInt = -128 := by
  rw [image_store_scalar, reference_big_reader]; decide +kernel
example : snapshot (store32 (store32 μ a (u 258)) b (u 513)) (wordObservation b) =
    List.replicate 30 0 ++ [2, 1] := by
  rw [image_overlap_backend]; decide +kernel
example : EvmYul.fromBytesBigEndian
    (snapshot (store32 (store32 μ a (u 258)) b (u 513)) (wordObservation b)) = 513 :=
  image_reference_reader (store32 μ a (u 258)) b (u 513)
example : (store32 μ a (u 258)).st = μ.st ∧ (store32 μ a (u 258)).key = μ.key :=
  store32_frame μ a (u 258)
example : μ.key.invocation ≠ μ.key.declaration := by decide

#print axioms reference_big_reader
#print axioms reference_array_reader
#print axioms reference_backend_bounded
#print axioms reference_word_toNat
#print axioms image_reference_reader
#print axioms image_reference_word
#print axioms image_reference_signed
end SolidityBridge.RoadmapV15.ReferenceReaderControls
