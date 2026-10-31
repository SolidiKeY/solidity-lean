import SolidityBridge.RoadmapV15.ReferenceImageTransport
import SolidityBridge.RoadmapV15.PreallocatedObservation

/-! Pure reference/image controls and actual supplied-opcode frame controls.
Both FrameKey pipeline identities are retained; no source compilation, allocator
or gas-checking driver execution is represented by these fixtures. -/
namespace SolidityBridge.RoadmapV15.ReferenceObservationControls
open Solidity Solidity.Backend Solidity.Evm.TryByteImage
open Solidity.Evm.External.Memory

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
private def μ (p : Pipeline) : FrameMem C [] :=
  { st := σ
    key := ⟨29, 2, p, 31, u 7, u 11, u 13⟩
    scalar := by intro R i; cases i
    capacity := 96
    aligned := ⟨3, rfl⟩
    data := fun _ => 0
    highWaterWords := 0
    resident := by decide
    zeroAbove := by intro i _; rfl }
private def a (p : Pipeline) : WordSpan (μ p).capacity := ⟨u 1, by change 1 + 32 ≤ 96; decide⟩
private def b (p : Pipeline) : WordSpan (μ p).capacity := ⟨u 2, by change 2 + 32 ≤ 96; decide⟩
private def c (p : Pipeline) : WordSpan (μ p).capacity := ⟨u 64, by change 64 + 32 ≤ 96; decide⟩
private def word258 : List UInt8 := List.replicate 30 0 ++ [1, 2]
private def word513 : List UInt8 := List.replicate 30 0 ++ [2, 1]

example (p : Pipeline) :
    [snapshot (store32 (μ p) (a p) (u 258)) (wordObservation (a p)),
      snapshot (store32 (store32 (μ p) (a p) (u 258)) (b p) (u 513)) (wordObservation (b p))] =
      [word258, word513] := by
  rw [image_pair_reference_bytes]
  simp only [reference_encoding_scalar, Scalar.encode_uint_toNat]
  decide +kernel
example : (store32 (μ .legacy) (a .legacy) (u 258)).key.pipeline = .legacy := rfl
example : (store32 (μ .viaIR) (a .viaIR) (u 258)).key.pipeline = .viaIR := rfl
example (p : Pipeline) : (store32 (μ p) (a p) (u 258)).st = σ := rfl
example (p : Pipeline) : snapshot
    (store32 (store32 (μ p) (a p) (u 258)) (c p) (u 513)) (wordObservation (a p)) = word258 := by
  rw [disjoint_image_reference_bytes (μ p) (a p) (c p) (u 258) (u 513) (Or.inl (by change 1 + 32 ≤ 64; decide))]
  rw [reference_encoding_scalar, Scalar.encode_uint_toNat]; decide +kernel
example (p : Pipeline) : snapshot
    (store32 (store32 (μ p) (a p) (u 258)) (b p) (u 513)) (wordObservation (a p)) ≠ word258 := by
  cases p <;> decide +kernel
example : [word258, word513] ≠ [word513, word258] := by decide +kernel
example : word258 ≠ word258.reverse := by decide +kernel
example : word258 ≠ (toBytesBE 31 258).toList := by decide +kernel

private def lo : EvmYul.UInt256 := Solidity.Evm.External.encode (258 : Scalar.Word).toFin
private def hi : EvmYul.UInt256 := Solidity.Evm.External.encode (513 : Scalar.Word).toFin
private def initial := populatedState lo hi
example : Represents 2 (populatedCore lo hi) initial.toMachineState := populated_represents lo hi
example : initial.memory.toList = word258 ++ word513 := by
  rw [initial, lo, hi, populated_backend_observation (258 : Scalar.Word) 513]; decide +kernel
example : initial.memory.toList.length = 64 := by
  rw [initial, lo, hi, populated_backend_observation (258 : Scalar.Word) 513]; decide +kernel
example : initial.memory.toList ≠ (populatedState hi lo).memory.toList := by
  rw [initial, lo, hi, populated_backend_observation (258 : Scalar.Word) 513,
    populated_backend_observation (513 : Scalar.Word) 258]; decide +kernel
example : initial.memory.toList ≠ word258 ++ word513 ++ [0] := by
  rw [initial, lo, hi, populated_backend_observation (258 : Scalar.Word) 513]; decide +kernel
example : initial.activeWords.toNat = 2 := rfl
example : ¬(2 < 2) := by decide
example : (initial.toMachineState.mload (address 0)).2 = initial.toMachineState :=
  populated_load_frame 258 513 ⟨0, by decide⟩
example : (initial.toMachineState.mload (address 1)).2 = initial.toMachineState :=
  populated_load_frame 258 513 ⟨1, by decide⟩
-- Positive fuel is essential; an exceptional resource stop is not Solidity revert.
example : EvmYul.EVM.step 0 0 (some (.MLOAD, none))
    {initial with stack := [address 1, lo, hi]} = .error .OutOfFuel := rfl
example : EvmYul.EVM.step 1 0 (some (.MLOAD, none))
    {initial with stack := [address 1, lo, hi]} =
      .ok (loaded {initial with stack := [address 1, lo, hi]} (address 1) [lo, hi]) :=
  (populated_supplied_load 258 513 ⟨1, by decide⟩ [lo, hi] 0).1
example : (loaded {initial with stack := [address 1, lo, hi]} (address 1) [lo, hi]).memory.toList =
    word258 ++ word513 := by
  have h := (populated_supplied_load 258 513 ⟨1, by decide⟩ [lo, hi] 0).2
  exact h.trans (by decide +kernel)
private def negativeOne : PrimTy.int.Denote := ⟨-1, by decide⟩
example : (populatedState
    (Solidity.Evm.External.encode (Scalar.encodeValue .int negativeOne).toFin) hi).memory.toList =
      List.replicate 32 255 ++ word513 := by
  change (populatedState
    (Solidity.Evm.External.encode (Scalar.encodeValue .int negativeOne).toFin)
    (Solidity.Evm.External.encode (Scalar.encodeValue .uint (u 513)).toFin)).memory.toList = _
  rw [populated_typed_observation .int .uint negativeOne (u 513)]
  decide +kernel

#print axioms typed_image_reference_bytes
#print axioms typed_image_reference_observation
#print axioms image_pair_reference_bytes
#print axioms disjoint_image_reference_bytes
#print axioms populated_backend_observation
#print axioms populated_typed_observation
#print axioms populated_load_frame
#print axioms populated_supplied_load
end SolidityBridge.RoadmapV15.ReferenceObservationControls
