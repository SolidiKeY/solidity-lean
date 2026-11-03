import Solidity.Hash.Adaptive
import Solidity.Storage.HashedKeccak
import SolidityBridge.ExternalEvm.StorageOpcode
import SolidityBridge.ExternalEvm.MemoryBytes

/-! Actual pinned EVM hash queries. Native KEC stays opaque; no correspondence
with mathematical keccak or random-oracle distribution is assumed here. -/
namespace Solidity.HashBridge
open EvmYul

def byteQuery (bytes : ByteArray) : List Nat := bytes.data.toList.map UInt8.toNat

def queryBytes (bytes : List Nat) : ByteArray := (bytes.map UInt8.ofNat).toByteArray

def actualDigest (bytes : ByteArray) : UInt256 :=
  .ofNat (fromByteArrayBigEndian (ffi.KEC bytes))

def actualHash (bytes : List Nat) : Nat := (actualDigest (queryBytes bytes)).toNat

theorem query_roundtrip (bytes : ByteArray) : queryBytes (byteQuery bytes) = bytes := by
  apply ByteArray.ext
  rw [queryBytes,Solidity.Evm.External.Memory.list_bytes]
  simp only [byteQuery,List.map_map,Function.comp_def,UInt8.ofNat_toNat,List.map_id',Array.toArray_toList]

theorem actual_query_result (bytes : ByteArray) :
    actualHash (byteQuery bytes) = (actualDigest bytes).toNat := by
  unfold actualHash
  rw [query_roundtrip]

theorem actual_hash_bound (bytes : List Nat) : actualHash bytes < 2^256 :=
  (actualDigest (queryBytes bytes)).val.isLt

def machineQuery (m : MachineState) (offset size : UInt256) : ByteArray :=
  m.memory.readWithPadding offset.toNat size.toNat

theorem machine_query_result (m : MachineState) (offset size : UInt256) :
    (m.keccak256 offset size).1 = actualDigest (machineQuery m offset size) := rfl

theorem machine_query_frame (m : MachineState) (offset size : UInt256) :
    (m.keccak256 offset size).2.memory = m.memory ∧
    (m.keccak256 offset size).2.activeWords = .ofNat
      (MachineState.M m.activeWords.toNat offset.toNat size.toNat) ∧
    (m.keccak256 offset size).2.gasAvailable = m.gasAvailable ∧
    (m.keccak256 offset size).2.returnData = m.returnData ∧
    (m.keccak256 offset size).2.H_return = m.H_return := ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Actual existing step component at fuel1/cost0, not the fetched/charged X driver. -/
theorem keccak_step_query (s : EvmYul.EVM.State) (offset size : UInt256)
    (tail : List UInt256) (hs : s.stack = offset :: size :: tail) :
    ∃ out, EvmYul.EVM.step 1 0 (some (.KECCAK256,none)) s = .ok out ∧
      out.stack = actualDigest (machineQuery s.toMachineState offset size) :: tail ∧
      out.toState = s.toState ∧ out.memory = s.memory := by
  rcases Solidity.Evm.StorageSlots.keccak_step s offset size tail hs with
    ⟨out,step,stack,world,memory⟩
  exact ⟨out,step,stack,world,memory⟩

/-- A query actually fed to the operation has this exact numeric hash, without
assuming the native provider agrees with a different mathematical algorithm. -/
theorem machine_query_natural (m : MachineState) (offset size : UInt256) :
    (m.keccak256 offset size).1.toNat =
      actualHash (byteQuery (machineQuery m offset size)) := by
  rw [machine_query_result,actual_query_result]

/-- Truncating arbitrary Nat inputs is not injective; use actual byte queries. -/
theorem raw_nat_truncation_control : queryBytes [0] = queryBytes [256] := by
  decide +kernel

end Solidity.HashBridge
