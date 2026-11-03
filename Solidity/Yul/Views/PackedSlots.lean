import Solidity.Yul.Views.PackedAggregates
import Solidity.Yul.Views.StorageContract
import Solidity.Yul.Views.WordMemory

/-! Concrete low-byte-coordinate storage serialization. Numeric slot maps
remain intrinsic Words, and every inverse byte read requires the nonwrapping
coordinate bound. HashedLayout supplies the base via physicalSlot; separation
from other logical regions remains the existing owner's real obligation. -/
namespace Solidity.Yul.Views

def slotBytes (m : SlotView) (a : Nat) : UInt8 :=
  wordByte (m ⟨(a / 32) % (2 ^ 256), Nat.mod_lt _ (by decide)⟩)
    (reverseByteIndex 32 ⟨a % 32, Nat.mod_lt _ (by decide)⟩)

def slotsOfBytes (m : ByteView) : SlotView :=
  fun s => mload (fun i => m (s.val * 32 + (31 - i % 32))) 0

theorem slotsOfBytes_slotBytes (m : SlotView) : slotsOfBytes (slotBytes m) = m := by
  funext s
  calc
    _ = mload (mstore (fun _ => 0) 0 (m s)) 0 := by
      apply mload_congr
      intro i
      simp only [Nat.zero_add]
      rw [show mstore (fun _ => 0) 0 (m s) i.val = wordByte (m s) i from
        by simpa only [Nat.zero_add] using find_mstore (fun _ => 0) 0 (m s) i]
      have hi := i.isLt
      have hd : (s.val * 32 + (31 - i.val)) / 32 = s.val := by omega
      have hr : (s.val * 32 + (31 - i.val)) % 32 = 31 - i.val := by omega
      simp only [Nat.mod_eq_of_lt hi, slotBytes, hd, hr, Nat.mod_eq_of_lt s.isLt]
      congr 1
      apply Fin.ext
      simp only [reverseByteIndex]
      omega
    _ = _ := mload_mstore _ _ _

theorem slotBytes_slotsOfBytes (m : ByteView) (a : Nat) (h : a < (2 ^ 256) * 32) :
    slotBytes (slotsOfBytes m) a = m a := by
  have hq : a / 32 < 2 ^ 256 := by omega
  have hr : a % 32 < 32 := Nat.mod_lt _ (by decide)
  unfold slotBytes slotsOfBytes
  rw [wordByte_mload]
  simp only [reverseByteIndex, Nat.zero_add, Nat.mod_eq_of_lt hq]
  have hc : 31 - a % 32 < 32 := by omega
  rw [Nat.mod_eq_of_lt hc]
  congr 1
  have := Nat.mod_add_div a 32
  omega

/-- A constructive typed-member patch, serialized back into physical words. -/
def PackedMembers.encodeSlots {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (ds : Source.DataList D τs) (base : Roadmap.Word)
    (_ : cs.Fits base) (m : SlotView) : Option SlotView :=
  (cs.encode ds (base.val * 32) (slotBytes m)).map slotsOfBytes

theorem PackedMembers.slot_roundtrip {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (ds : Source.DataList D τs) (base : Roadmap.Word)
    (fits : cs.Fits base) (m : SlotView) (out : ByteView)
    (e : cs.encode ds (base.val * 32) (slotBytes m) = some out) :
    cs.decode (base.val * 32) (slotBytes (slotsOfBytes out)) = some ds := by
  calc
    _ = cs.decode (base.val * 32) out := cs.decode_congr _ _ _ (fun a ha => by
      apply slotBytes_slotsOfBytes
      have hb := cs.owned_bounds _ a ha
      exact Nat.lt_of_lt_of_le hb.2 fits)
    _ = _ := cs.decode_encode ds _ _ out e

/-- Residual bytes are preserved even inside slots that contain owned fields. -/
theorem PackedMembers.slot_residual_byte {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (ds : Source.DataList D τs) (base : Roadmap.Word)
    (m : SlotView) (out : ByteView)
    (e : cs.encode ds (base.val * 32) (slotBytes m) = some out)
    (a : Nat) (bound : a < (2 ^ 256) * 32) (unowned : ¬ cs.owns (base.val * 32) a) :
    slotBytes (slotsOfBytes out) a = slotBytes m a := by
  rw [slotBytes_slotsOfBytes out a bound]
  exact cs.encode_residual ds _ _ out e a unowned

theorem PackedMembers.slot_unchanged {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (ds : Source.DataList D τs) (base : Roadmap.Word)
    (fits : cs.Fits base) (m : SlotView) (h : cs.matches ds (base.val * 32) (slotBytes m)) :
    cs.encodeSlots ds base fits m = some m := by
  simp only [PackedMembers.encodeSlots, cs.encode_unchanged ds _ _ h,
    Option.map_some, slotsOfBytes_slotBytes]

end Solidity.Yul.Views
