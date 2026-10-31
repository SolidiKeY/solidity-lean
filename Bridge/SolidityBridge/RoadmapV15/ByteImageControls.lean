import SolidityBridge.RoadmapV15.ByteImageTransport

/-! Inhabited pure-image controls. Complete lists matter; these are neither
physical reference execution nor allocator/resource witnesses. -/
namespace SolidityBridge.RoadmapV15.ByteImageControls
open Solidity Solidity.Backend Solidity.Evm.TryByteImage

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
    key := ⟨17, 2, .viaIR, 23, u 7, u 11, u 13⟩
    scalar := by intro R i; cases i
    capacity := 96
    aligned := ⟨3, rfl⟩
    data := fun _ => 0
    highWaterWords := 0
    resident := by decide
    zeroAbove := by intro i _; rfl }
private def a : WordSpan μ.capacity := ⟨u 1, by decide⟩
private def b : WordSpan μ.capacity := ⟨u 2, by decide⟩
private def c : WordSpan μ.capacity := ⟨u 64, by decide⟩
private def z : WordSpan μ.capacity := ⟨u 0, by decide⟩
private def word258 : List UInt8 := List.replicate 30 0 ++ [1, 2]
private theorem bytes258 : (toBytesBE 32 258).toList = word258 := by decide +kernel
private theorem bytes513 : (toBytesBE 32 513).toList = List.replicate 30 0 ++ [2, 1] := by
  decide +kernel

-- The same theorem covers genuinely aligned zero and unaligned one.
example : snapshot (store32 μ a (u 258)) (wordObservation a) = word258 :=
  (image_store_backend μ a (u 258)).trans bytes258
example : snapshot (store32 μ z (u 258)) (wordObservation z) = word258 :=
  (image_store_backend μ z (u 258)).trans bytes258
example : (store32 μ a (u 258)).st = μ.st ∧ (store32 μ a (u 258)).key = μ.key :=
  store32_frame μ a (u 258)
example : (store32 μ a (u 258)).key.invocation = 17 ∧
    (store32 μ a (u 258)).key.declaration = 23 ∧
    (store32 μ a (u 258)).st.selfBalance.val = 13 := by decide +kernel
example : (store32 μ a (u 258)).data ⟨0, by decide⟩ = μ.data ⟨0, by decide⟩ :=
  image_store_surrounding μ a (u 258) _ (Or.inl (by decide))
example : (store32 μ a (u 258)).data ⟨33, by decide⟩ = μ.data ⟨33, by decide⟩ :=
  image_store_surrounding μ a (u 258) _ (Or.inr (by decide))
example : ofBytesBE (snapshot (store32 μ a (u 258)) (wordObservation a)) = 258 :=
  image_store_read μ a (u 258)

-- Overlapping intervals [1,33) and [2,34); full later word, not just its tail.
example : snapshot (store32 (store32 μ a (u 258)) b (u 513)) (wordObservation b) =
    List.replicate 30 0 ++ [2, 1] :=
  (image_overlap_backend μ a b (u 258) (u 513)).trans bytes513
-- The earlier observation is actually changed; preserving it would be false.
example : snapshot (store32 (store32 μ a (u 258)) b (u 513)) (wordObservation a) =
    List.replicate 31 0 ++ [2] := by decide +kernel
example : snapshot (store32 (store32 μ a (u 258)) b (u 513)) (wordObservation a) ≠
    word258 := by decide +kernel
-- Nonoverlap and exact upper capacity boundary [64,96).
example : snapshot (store32 (store32 μ a (u 258)) c (u 513)) (wordObservation a) =
    word258 := (image_disjoint_backend μ a c (u 258) (u 513) (Or.inl (by decide))).trans bytes258
example : snapshot (store32 μ c (u 513)) (wordObservation c) =
    List.replicate 30 0 ++ [2, 1] := (image_store_backend μ c (u 513)).trans bytes513
private def emptyFar : ByteSpan μ.capacity := ⟨u (2 ^ 256 - 1) (by decide +kernel), u 0, Or.inl rfl⟩
example : snapshot μ emptyFar = [] := snapshot_empty μ emptyFar rfl
example : ¬ ((u 65).val.toNat + 32 ≤ μ.capacity) := by decide
example : (snapshot (store32 μ a (u 258)) (wordObservation a)).length = 32 :=
  snapshot_length _ _
-- Wrong length, wrong endian and word order all change complete observations.
example : word258 ≠ (toBytesBE 31 258).toList := by decide +kernel
example : word258 ≠ (toBytesBE 33 258).toList := by decide +kernel
example : word258 ≠ word258.reverse := by decide +kernel
example : snapshot (store32 μ a (u 258)) (wordObservation a) ≠
    snapshot (store32 μ a (u 513)) (wordObservation a) := by
  rw [image_store_backend, image_store_backend]; decide +kernel
example : word258 ++ (toBytesBE 32 513).toList ≠ (toBytesBE 32 513).toList ++ word258 := by
  decide +kernel
private def negativeOne : PrimTy.int.Denote := ⟨-1, by decide⟩
private def minimumSigned : PrimTy.int.Denote := ⟨-((2 ^ 255 : Nat) : Int), by decide +kernel⟩
example : snapshot (store32 μ a (PrimTy.toWord negativeOne)) (wordObservation a) =
    List.replicate 32 255 := by rw [image_store_typed μ a .int negativeOne]; decide +kernel
example : snapshot (store32 μ a (PrimTy.toWord minimumSigned)) (wordObservation a) =
    128 :: List.replicate 31 0 := by rw [image_store_typed μ a .int minimumSigned]; decide +kernel
example : (Scalar.immediate (snapshot (store32 μ a (PrimTy.toWord minimumSigned))
    (wordObservation a))).toInt = -((2 ^ 255 : Nat) : Int) := image_store_signed μ a minimumSigned
example : snapshot (store32 μ a (u (2 ^ 256 - 1) (by decide +kernel))) (wordObservation a) =
    List.replicate 32 255 := by rw [image_store_backend]; decide +kernel
example : snapshot (store32 μ a (imageScalarWord (BitVec.ofNat 256 (2 ^ 256 + 258))))
    (wordObservation a) = word258 := by rw [image_store_scalar]; decide +kernel
example : snapshot (store32 μ a (imageScalarWord (Scalar.unsignedClean ⟨0, by decide⟩ 257)))
    (wordObservation a) = List.replicate 31 0 ++ [1] := by rw [image_store_scalar]; decide +kernel
example : snapshot (store32 μ a (imageScalarWord (Scalar.signedClean ⟨0, by decide⟩ 128)))
    (wordObservation a) = List.replicate 31 255 ++ [128] := by rw [image_store_scalar]; decide +kernel
example : Scalar.run (Scalar.unsignedCode ⟨0, by decide⟩)
    (Scalar.immediate (snapshot (store32 μ a (imageScalarWord 257)) (wordObservation a)) :: [9]) =
    some (Scalar.immediate (snapshot (store32 μ a
      (imageScalarWord (Scalar.unsignedClean ⟨0, by decide⟩ 257))) (wordObservation a)) :: [9]) :=
  image_unsigned_cleanup μ a ⟨0, by decide⟩ 257 [9]
example : Scalar.run (Scalar.signedCode ⟨0, by decide⟩)
    (Scalar.immediate (snapshot (store32 μ a (imageScalarWord 128)) (wordObservation a)) :: [9]) =
    some (Scalar.immediate (snapshot (store32 μ a
      (imageScalarWord (Scalar.signedClean ⟨0, by decide⟩ 128))) (wordObservation a)) :: [9]) :=
  image_signed_cleanup μ a ⟨0, by decide⟩ 128 [9]

#print axioms backend_byte_at
#print axioms image_wordByte_backend
#print axioms image_store_backend
#print axioms image_store_observation
#print axioms image_store_surrounding
#print axioms image_store_read
#print axioms image_store_typed
#print axioms image_store_signed
#print axioms image_overlap_backend
#print axioms image_disjoint_backend
#print axioms image_store_modulo
#print axioms image_store_scalar
#print axioms image_unsigned_cleanup
#print axioms image_signed_cleanup
end SolidityBridge.RoadmapV15.ByteImageControls
