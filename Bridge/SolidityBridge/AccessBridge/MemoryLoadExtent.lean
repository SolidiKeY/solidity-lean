import SolidityBridge.AccessBridge.MemoryLoadExtentInterface
import SolidityBridge.AccessBridge.MemoryLoad

/-! Exact raw MLOAD extent and the published P6 touch image. This adds no
admission restriction and makes no charged-success or Source-origin claim. -/
namespace SolidityBridge.AccessBridge.MemoryLoadExtent
open Solidity Solidity.Backend EvmYul
open Solidity.Evm.TryByteImage

theorem active (native : EvmYul.MachineState) (offset : UInt256) :
    (native.mload offset).2.activeWords.toNat =
      max native.activeWords.toNat ((offset.toNat+63)/32) := by
  change (max native.activeWords.toNat ((offset.toNat+32+31)/32)) % UInt256.size = _
  have add : offset.toNat+32+31=offset.toNat+63 := by omega
  rw [add]
  apply Nat.mod_eq_of_lt
  have old : native.activeWords.toNat<UInt256.size := native.activeWords.val.isLt
  have bound : offset.toNat<UInt256.size := offset.val.isLt
  have size : 64<UInt256.size := by decide
  omega

theorem post_image {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
    (native : EvmYul.MachineState) (span : ByteSpan frame.capacity) (offset : UInt256)
    (same : offset.toNat=span.offset.val.toNat) (length : span.length.val.toNat=32)
    (image : FrameImage frame native) :
    (FrameImage (Yul.Adapters.P6ByteMemory.touch frame span) (native.mload offset).2 ↔
    32*(Yul.Adapters.P6ByteMemory.touch frame span).highWaterWords<UInt256.size) := by
  constructor
  · intro post
    exact post.wordFit
  · intro fit
    refine ⟨?_,?_,fit⟩
    · intro address
      rw [MemoryLoad.unchanged_bytes, Yul.Adapters.P6ByteMemory.touch_image]
      exact image.bytes address
    · rw [active, image.active, same]
      simp only [Yul.Adapters.P6ByteMemory.touch, length]
      rfl

def certificate : MemoryLoadExtentCertificate where
  active := active
  post_image := post_image

/-- info: 'SolidityBridge.AccessBridge.MemoryLoadExtent.active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms active
/-- info: 'SolidityBridge.AccessBridge.MemoryLoadExtent.post_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms post_image
/-- info: 'SolidityBridge.AccessBridge.MemoryLoadExtent.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end SolidityBridge.AccessBridge.MemoryLoadExtent
