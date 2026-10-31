import SolidityBridge.RoadmapV15.ReferenceEncoding
import SolidityBridge.ExternalEvm.MemoryComposition

/-! Consumers of the published FFI-independent two-cell reference constructor.
These are preallocated numeric representations, not a physical allocator or a
compiler symbolic-path relation. MLOAD results are deliberately left as the
actual lookup expression: the missing padding/read-value contract is not supplied.
The supplied-opcode step below has positive fuel and zero charged gas, and does
not discharge X admissibility, fetched-code reachability or Osaka agreement. -/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Backend
open Solidity.Evm.External.Memory

/-- All64 physical bytes of the existing reference constructor, including order. -/
theorem populated_backend_observation (lo hi : Scalar.Word) :
    (populatedState (Solidity.Evm.External.encode lo.toFin)
      (Solidity.Evm.External.encode hi.toFin)).memory.toList =
      (toBytesBE 32 lo.toNat).toList ++ (toBytesBE 32 hi.toNat).toList := by
  change (encoding (Solidity.Evm.External.encode lo.toFin) ++
    encoding (Solidity.Evm.External.encode hi.toFin)).toList = _
  rw [bytes_list, ByteArray.data_append, Array.toList_append]
  rw [← bytes_list, ← bytes_list, reference_encoding_scalar, reference_encoding_scalar]

/-- Actual typed scalar/ABI encodings inhabit that pure reference memory. -/
theorem populated_typed_observation (p q : PrimTy) (v : p.Denote) (w : q.Denote) :
    (populatedState (Solidity.Evm.External.encode (Scalar.encodeValue p v).toFin)
      (Solidity.Evm.External.encode (Scalar.encodeValue q w).toFin)).memory.toList =
      (toBytesBE 32 (PrimTy.toWord v).val.toNat).toList ++
      (toBytesBE 32 (PrimTy.toWord w).val.toNat).toList := by
  rw [populated_backend_observation, typed_bytes_toWord, typed_bytes_toWord]

/-- The published relation supplies a non-vacuous in-capacity load frame without
assuming its returned word. This is a real MachineState equality, not a journal. -/
theorem populated_load_frame (lo hi : Scalar.Word) (i : Fin 2) :
    ((populatedState (Solidity.Evm.External.encode lo.toFin)
      (Solidity.Evm.External.encode hi.toFin)).toMachineState.mload (address i.val)).2 =
      (populatedState (Solidity.Evm.External.encode lo.toFin)
        (Solidity.Evm.External.encode hi.toFin)).toMachineState := by
  have h := load_state_frame 2 _ _
    (populated_represents (Solidity.Evm.External.encode lo.toFin)
      (Solidity.Evm.External.encode hi.toFin)) i.val i.isLt
  exact congrArg Prod.snd h

/-- Actual supplied-opcode dispatch plus all64 output bytes. No read-value,
serialization, gas adequacy, stack-height or driver-success premise is hidden. -/
theorem populated_supplied_load (lo hi : Scalar.Word) (i : Fin 2)
    (tail : List EvmYul.UInt256) (fuel : Nat) :
    let s := populatedState (Solidity.Evm.External.encode lo.toFin)
      (Solidity.Evm.External.encode hi.toFin)
    EvmYul.EVM.step (fuel + 1) 0 (some (.MLOAD, none))
      {s with stack := address i.val :: tail} =
        .ok (loaded {s with stack := address i.val :: tail} (address i.val) tail) ∧
    (loaded {s with stack := address i.val :: tail} (address i.val) tail).memory.toList =
      (toBytesBE 32 lo.toNat).toList ++ (toBytesBE 32 hi.toNat).toList := by
  dsimp only []
  constructor
  · exact load_dispatch _ (address i.val) tail fuel
  · change (populatedState (Solidity.Evm.External.encode lo.toFin)
      (Solidity.Evm.External.encode hi.toFin)).memory.toList = _
    exact populated_backend_observation lo hi

end SolidityBridge.RoadmapV15
