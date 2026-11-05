import SolidityBridge.AccessBridge.MemoryLoadInterface
import SolidityBridge.AccessBridge.MemoryCharged
import SolidityBridge.ExternalEvm.PaddingInterface

/-! Actual padded memory reads over the frozen P6 image. This is an adapter
for existing readers, not a replacement memory, source evaluator or gas model. -/
namespace SolidityBridge.AccessBridge.MemoryLoad
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Evm.TryByteImage
open SolidityBridge.RoadmapV15

theorem readWithout_source (source : ByteArray) (offset width : Nat) :
    (source.readWithoutPadding offset width).data.toList =
      (source.data.toList.drop offset).take width := by
  unfold ByteArray.readWithoutPadding
  split
  next beyond =>
    have nil : source.data.toList.drop offset = [] := List.drop_eq_nil_iff.mpr beyond
    rw [nil]
    simp only [List.take_nil]
    rfl
  next inside =>
    simp only [ByteArray.extract, ByteArray.copySlice, ByteArray.empty, ByteArray.emptyWithCapacity,
      Array.extract_empty, Array.empty_append, Array.append_empty, Array.toList_extract,
      List.extract, Nat.add_sub_cancel_left]
    by_cases fits : width ≤ source.size
    · rw [Nat.min_eq_left fits]
    · have dropped : (source.data.toList.drop offset).length ≤ source.size := by
        simp only [List.length_drop, Array.length_toList]
        exact Nat.sub_le _ _
      rw [Nat.min_eq_right (by omega), List.take_of_length_le dropped,
        List.take_of_length_le (Nat.le_trans dropped (by omega))]

/-- Only the requested byte count has a host-width bound. No offset or source
buffer bound is imposed. Fixed MLOAD count32 discharges this bound universally. -/
theorem readWith_source (source : ByteArray) (offset width : Nat)
    (host : width < USize.size) :
    (source.readWithPadding offset width).data.toList =
      Source.fitBytes width (source.data.toList.drop offset) := by
  let segment := source.readWithoutPadding offset width
  have raw : segment.data.toList = (source.data.toList.drop offset).take width :=
    readWithout_source source offset width
  have length : segment.size = min width (source.data.toList.drop offset).length := by
    change segment.data.size = _
    rw [← Array.length_toList, raw, List.length_take]
  have limited : segment.size ≤ width := by
    rw [length]
    exact Nat.min_le_left _ _
  have padding := Memory.zeroes_difference width segment.size host limited
  have supported : ¬ width ≥ 2^64 := Nat.not_le.mpr (Nat.lt_of_lt_of_le host USize.size_le)
  rw [ByteArray.readWithPadding, if_neg supported]
  change (segment ++ ffi.ByteArray.zeroes
    (⟨(width : BitVec System.Platform.numBits) -
      (segment.size : BitVec System.Platform.numBits)⟩ : USize)).data.toList = _
  rw [padding, ByteArray.data_append, Array.toList_append]
  simp only [Array.toList_replicate, raw]
  have difference : width - segment.size = width - (source.data.toList.drop offset).length := by
    rw [length]
    omega
  rw [difference]
  simp only [Source.fitBytes, List.take_append, List.take_replicate,
    Nat.min_eq_left (Nat.sub_le width _)]

/-- The existing fitBytes list is the existing zero-extended byte-memory reader. -/
theorem fitBytes_read (bytes : List UInt8) (offset width : Nat) :
    Source.fitBytes width (bytes.drop offset) =
      Environment.readMemory (fun address => bytes[address]?.getD 0) offset width := by
  apply List.ext_getElem
  · simp only [Source.fitBytes_length, Environment.readMemory, List.length_map, List.length_range]
  · intro i hi hj
    have small : i < width := by simpa only [Source.fitBytes_length] using hi
    simp only [Environment.readMemory, List.getElem_map, List.getElem_range]
    simp only [Source.fitBytes, List.getElem_take]
    by_cases present : i < (bytes.drop offset).length
    · rw [List.getElem_append_left present]
      rw [← List.getElem?_drop, List.getElem?_eq_getElem present, Option.getD_some]
    · rw [List.getElem_append_right (Nat.le_of_not_lt present), List.getElem_replicate]
      rw [← List.getElem?_drop, List.getElem?_eq_none (Nat.le_of_not_lt present), Option.getD_none]

theorem frame_zero {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ) (address : Nat)
    (above : 32 * frame.highWaterWords ≤ address) :
    MemoryOps.Physical.frameBytes frame address = 0 := by
  unfold MemoryOps.Physical.frameBytes
  split
  next fits =>
    apply frame.zeroAbove
    simpa only [Nat.mul_comm] using above
  next exterior => rfl

theorem read_image {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
    (native : EvmYul.MachineState) (image : FrameImage frame native) (offset : Nat) :
    (native.memory.readWithPadding offset 32).data.toList =
      Environment.readMemory (MemoryOps.Physical.frameBytes frame) offset 32 := by
  have host : 32 < USize.size :=
    Nat.lt_of_lt_of_le (by decide : 32 < 2^32) USize.le_size
  have bytes : (fun address => native.memory.data.toList[address]?.getD 0) =
      MemoryOps.Physical.frameBytes frame := funext image.bytes
  rw [readWith_source _ _ _ host, fitBytes_read, bytes]

private theorem read_zero (memory : Environment.Memory) (offset : Nat)
    (zero : ∀ j, j < 32 → memory (offset+j) = 0) :
    ofBytesBE (Environment.readMemory memory offset 32) = 0 := by
  have bytes : Environment.readMemory memory offset 32 = List.replicate 32 0 := by
    apply List.ext_getElem
    · simp only [Environment.readMemory, List.length_map, List.length_range, List.length_replicate]
    · intro j hj hk
      simp only [Environment.readMemory, List.getElem_map, List.getElem_range, List.getElem_replicate]
      apply zero j
      simpa only [Environment.readMemory, List.length_map, List.length_range] using hj
  rw [bytes]
  decide +kernel

theorem payload {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
    (native : EvmYul.MachineState) (offset : UInt256) (image : FrameImage frame native) :
    (native.mload offset).1.toNat = ofBytesBE
      (Environment.readMemory (MemoryOps.Physical.frameBytes frame) offset.toNat 32) := by
  change (native.lookupMemory offset).toNat = _
  rw [EvmYul.MachineState.lookupMemory]
  by_cases guard : offset.toNat ≥ native.memory.size ∨ offset ≥ native.activeWords * ⟨32⟩
  · rw [if_pos guard]
    symm
    apply read_zero
    intro j hj
    rcases guard with beyond | above
    · have missing : native.memory.data.toList[offset.toNat+j]? = none :=
        List.getElem?_eq_none (by change native.memory.size ≤ offset.toNat+j; omega)
      rw [← image.bytes (offset.toNat+j), missing]
      rfl
    · change native.msize.toNat ≤ offset.toNat at above
      rw [MemoryCharged.size_payload frame native image] at above
      exact frame_zero frame _ (by omega)
  · rw [if_neg guard]
    change EvmYul.fromByteArrayBigEndian (native.memory.readWithPadding offset.toNat 32) % UInt256.size = _
    rw [reference_array_reader, Memory.bytes_list, read_image frame native image]
    have bounded : ofBytesBE
        (Environment.readMemory (MemoryOps.Physical.frameBytes frame) offset.toNat 32) < UInt256.size := by
      have bytes := bytes_value_bound
        (Environment.readMemory (MemoryOps.Physical.frameBytes frame) offset.toNat 32)
      simpa only [Environment.readMemory, List.length_map, List.length_range] using bytes
    exact Nat.mod_eq_of_lt bounded

theorem unchanged_bytes (native : EvmYul.MachineState) (offset : UInt256) :
    (native.mload offset).2.memory = native.memory := by rfl

def certificate : MemoryLoadCertificate where
  payload := fun frame native offset image => payload frame native offset image
  unchanged_bytes := unchanged_bytes

/-- Logical byte installation in an existing native machine. This is an
initial relation witness, not a native allocator or Source-origin certificate. -/
def installed {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
    (native : EvmYul.MachineState) : EvmYul.MachineState :=
  {native with
    memory := ⟨(List.ofFn frame.data).toArray⟩
    activeWords := UInt256.ofNat frame.highWaterWords}

theorem installed_image {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
    (native : EvmYul.MachineState) (fits : 32 * frame.highWaterWords < UInt256.size) :
    FrameImage frame (installed frame native) := by
  refine ⟨?_,?_,fits⟩
  · intro address
    change (List.ofFn frame.data)[address]?.getD 0 = MemoryOps.Physical.frameBytes frame address
    by_cases inside : address < frame.capacity
    · rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using inside)]
      simp only [Option.getD_some, List.getElem_ofFn, MemoryOps.Physical.frameBytes, dif_pos inside]
    · rw [List.getElem?_eq_none (by simpa only [List.length_ofFn] using Nat.le_of_not_lt inside)]
      simp only [Option.getD_none, MemoryOps.Physical.frameBytes, dif_neg inside]
  · change frame.highWaterWords % UInt256.size = frame.highWaterWords
    exact Nat.mod_eq_of_lt (by omega)

/-- info: 'SolidityBridge.AccessBridge.MemoryLoad.installed_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms installed_image
/-- info: 'SolidityBridge.AccessBridge.MemoryLoad.frame_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms frame_zero
/-- info: 'SolidityBridge.AccessBridge.MemoryLoad.read_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_image
/-- info: 'SolidityBridge.AccessBridge.MemoryLoad.payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payload
/-- info: 'SolidityBridge.AccessBridge.MemoryLoad.unchanged_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unchanged_bytes
/-- info: 'SolidityBridge.AccessBridge.MemoryLoad.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
/-- info: 'SolidityBridge.AccessBridge.MemoryLoad.fitBytes_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fitBytes_read
/-- info: 'SolidityBridge.AccessBridge.MemoryLoad.readWithout_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readWithout_source
/-- info: 'SolidityBridge.AccessBridge.MemoryLoad.readWith_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readWith_source
end SolidityBridge.AccessBridge.MemoryLoad
