import SolidityBridge.RoadmapV15.P10.MetadataPushConsumer
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Complete metadata constant observations. Numeric selector versus left-aligned
ABI bytes4 remains distinct; pure payload facts do not prove an allocator. -/
namespace SolidityBridge.RoadmapV15.P10.MetadataPushControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External WordPushFixtures

def words : List Backend.Environment.Word := [lenU 258 (by decide),lenU 513 (by decide)]
def zeroValue : Fin (256^0) := ⟨0,by decide⟩
def byteValue : Fin (256^1) := ⟨0xa5,by decide⟩
def selector : Fin (2^32) := ⟨0x12345678,by decide⟩
def selectorValue : Fin (256^4) := ⟨selector.val,by decide⟩
def fullValue : Fin (256^32) := ⟨(2^256 : Nat)-1,by decide⟩

def expected (perm : Bool) (width : Fin 33) (value : Fin (256^width.val))
    (tail : List Backend.Environment.Word) : EVM.State :=
  {metadataPushInput (seed 10 perm) before after width value tail with
    pc := u (4+width.val),gasAvailable := u (10-metadataPushCost width),execLength := 42
    stack := UInt256.ofNat value.val::tail.map (fun w => UInt256.mk (Scalar.encodeValue .uint w).toFin)}

theorem populated (valid : Array UInt256) (perm : Bool) (width : Fin 33)
    (value : Fin (256^width.val)) (tail : List Backend.Environment.Word) (room : tail.length+1 ≤ 1024) :
    Assembly.driverSteps 1 2 valid (metadataPushInput (seed 10 perm) before after width value tail) =
      .ok (expected perm width value tail) := by
  have h := (metadata_constant_execution valid (seed 10 perm) before after width value tail (by decide)
    (by change metadataPushCost width ≤ 10;unfold metadataPushCost;split <;> decide) room 0).2.1
  have gasEq : (seed 10 perm).gasAvailable-UInt256.ofNat (metadataPushCost width) = u (10-metadataPushCost width) := by
    change u 10-UInt256.ofNat (metadataPushCost width) = _
    unfold metadataPushCost
    split <;> rfl
  have pcEq : UInt256.ofNat 3+UInt256.ofNat (width.val+1) = u (4+width.val) := by
    apply congrArg UInt256.mk
    apply Fin.ext
    change (3%UInt256.size+(width.val+1)%UInt256.size)%UInt256.size = (4+width.val)%UInt256.size
    rw [←Nat.add_mod]
    congr 1
    omega
  have same : (Assembly.chargedPrepare
      (metadataPushInput (seed 10 perm) before after width value tail) (metadataPushCost width)).replaceStackAndIncrPC (UInt256.ofNat value.val::
        (metadataPushInput (seed 10 perm) before after width value tail).stack) (width.val+1) =
      expected perm width value tail := by
    change ({metadataPushInput (seed 10 perm) before after width value tail with
      pc := UInt256.ofNat 3+UInt256.ofNat (width.val+1),
      gasAvailable := (seed 10 perm).gasAvailable-UInt256.ofNat (metadataPushCost width),
      execLength := 42,stack := UInt256.ofNat value.val::
        tail.map (fun w => UInt256.mk (Scalar.encodeValue .uint w).toFin)} : EVM.State) = _
    rw [gasEq,pcEq]
    rfl
  exact h.trans (congrArg Except.ok same)

theorem zero_byte_selector_full (valid : Array UInt256) :
    Assembly.driverSteps 1 2 valid (metadataPushInput (seed 10 false) before after 0 zeroValue words) =
      .ok (expected false 0 zeroValue words) ∧
    Assembly.driverSteps 1 2 valid (metadataPushInput (seed 10 true) before after 1 byteValue words) =
      .ok (expected true 1 byteValue words) ∧
    Assembly.driverSteps 1 2 valid (metadataPushInput (seed 10 false) before after 4 selectorValue words) =
      .ok (expected false 4 selectorValue words) ∧
    Assembly.driverSteps 1 2 valid (metadataPushInput (seed 10 true) before after 32 fullValue words) =
      .ok (expected true 32 fullValue words) := by
  exact ⟨populated valid false 0 zeroValue words (by decide),populated valid true 1 byteValue words (by decide),
    populated valid false 4 selectorValue words (by decide),populated valid true 32 fullValue words (by decide)⟩

theorem selector_alignment (valid : Array UInt256) :
    Backend.Environment.constant 4 selectorValue = Backend.Environment.selectorCode selector ∧
    Backend.Environment.selectorAbiCode selector = Backend.Environment.constant 32 (Backend.Environment.selectorAbiValue selector) ∧
    Assembly.driverSteps 1 2 valid (metadataPushInput (seed 10 true) before after 32
      (Backend.Environment.selectorAbiValue selector) words) =
      .ok (expected true 32 (Backend.Environment.selectorAbiValue selector) words) ∧
    (expected false 4 selectorValue words).stack = [u 0x12345678,u 258,u 513] ∧
    (expected true 32 (Backend.Environment.selectorAbiValue selector) words).stack ≠
      [u 0x12345678,u 258,u 513] := by
  exact ⟨rfl,rfl,populated valid true 32 (Backend.Environment.selectorAbiValue selector) words (by decide),rfl,by decide⟩

theorem capacity_and_empty (valid : Array UInt256) :
    Assembly.driverSteps 1 2 valid (metadataPushInput (seed 10 true) before after 0 zeroValue []) =
      .ok (expected true 0 zeroValue []) ∧
    Assembly.driverSteps 1 2 valid (metadataPushInput (seed 10 false) before after 1 byteValue
      (List.replicate 1023 (lenU 9 (by decide)))) =
      .ok (expected false 1 byteValue (List.replicate 1023 (lenU 9 (by decide)))) ∧
    Assembly.driverSteps 1 2 valid (metadataPushInput (seed 10 true) before after 0 zeroValue
      (List.replicate 1024 (lenU 9 (by decide)))) = .error .StackOverflow := by
  exact ⟨populated valid true 0 zeroValue [] (by decide),
    populated valid false 1 byteValue (List.replicate 1023 (lenU 9 (by decide)))
      (by simp only [List.length_replicate];omega),
    metadata_constant_full_stack valid (seed 10 true) before after 0 zeroValue
      (List.replicate 1024 (lenU 9 (by decide))) (by decide) (by decide)
      (by simp only [List.length_replicate]) 0⟩

theorem resource_refusals (valid : Array UInt256) :
    EVM.X 2 valid (metadataPushInput (seed 1 false) before after 0 zeroValue words) = .error .OutOfGass ∧
    EVM.X 2 valid (metadataPushInput (seed 2 true) before after 4 selectorValue words) = .error .OutOfGass ∧
    Assembly.driverSteps 1 1 valid (metadataPushInput (seed 10 true) before after 4 selectorValue words) = .error .OutOfFuel ∧
    (expected false 0 zeroValue words).gasAvailable = u 8 ∧
    (expected false 4 selectorValue words).gasAvailable = u 7 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem endian_and_order_negatives :
    (expected false 4 selectorValue words).executionEnv.code.data.toList =
      [0x60,0x7f,0x50,0x63,0x12,0x34,0x56,0x78,0x00] ∧
    (expected false 4 selectorValue words).executionEnv.code.data.toList ≠
      [0x60,0x7f,0x50,0x63,0x78,0x56,0x34,0x12,0x00] ∧
    (expected false 4 selectorValue words).executionEnv.code.data.toList.length = 9 ∧
    (expected false 4 selectorValue words).executionEnv.code.data.toList ≠
      [0x60,0x7f,0x50,0x63,0x12,0x34,0x56,0x00] ∧
    (expected false 4 selectorValue words).stack ≠ [u 0x78563412,u 258,u 513] ∧
    (expected false 4 selectorValue words).stack ≠ [u 513,u 258,u 0x12345678] ∧
    (expected false 0 zeroValue words).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x5f,0x00] ∧
    (expected false 4 selectorValue words).returnData.data.toList = [0xcc,0xdd] ∧
    (expected false 4 selectorValue words).H_return.data.toList = [0xee,0xff] ∧
    (expected false 4 selectorValue words).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (expected false 4 selectorValue words).memory = (seed 10 false).memory ∧
    (expected false 4 selectorValue words).accountMap = accounts ∧
    (expected false 4 selectorValue words).σ₀ = accounts ∧
    (expected false 4 selectorValue words).substate = (seed 10 false).substate := by
  exact ⟨by decide,by decide,by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms populated
#print axioms zero_byte_selector_full
#print axioms selector_alignment
#print axioms capacity_and_empty
#print axioms resource_refusals
#print axioms endian_and_order_negatives
end SolidityBridge.RoadmapV15.P10.MetadataPushControls
