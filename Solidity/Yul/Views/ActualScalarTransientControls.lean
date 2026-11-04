import Solidity.Yul.Views.ActualScalarTransient
import Solidity.Yul.Views.TransientSlotControls

/-! Actual metadata-selected transient writes share slot0 coordinates with a
persistent root while retaining separate banks. Nonzero raw padding survives
writes/reset. These scalar witnesses do not establish whole-registry reset. -/
namespace Solidity.Yul.Views.Controls

def atCell := (rootTempRegistry account)[0]'(by decide)
def atRaw : SlotView := fun _=>0xbeef0000
def atBefore : Source.EMState rootEnv [] :=
  ((Source.writeAt TransientSlotControls.frame (rootPath "a") (Source.intWrap rootU8 7)).run TransientSlotControls.state).2

def atWrite := actualScalarWrite TransientSlotControls.frame atCell.path atCell.codec atCell.slot
  (Source.intWrap unsigned16 0x1234) atRaw atBefore

theorem at_coordinate : (atCell.path,atCell.slot.val,atCell.field.offset,atCell.field.width)=
    (rootPath "temp",0,0,2) := rfl

theorem at_same_slot : atCell.slot=((rootRegistry account)[0]'(by decide)).slot := rfl

theorem at_raw : atWrite.2 0=0xbeef1234 := rfl

theorem at_read : (atWrite.1.2.2.ex.transient.cells account).read atCell.path=
    some (Source.intWrap unsigned16 0x1234) := rfl

theorem at_persistent_survives : (atWrite.1.2.2.ex.world.accounts account).storage.read (rootPath "a")=
    some (Source.intWrap rootU8 7) := rfl

theorem at_reencode : encodeScalarPath atCell.path atCell.codec atCell.slot
    (atWrite.1.2.2.ex.transient.cells account) atRaw=some atWrite.2 :=
  actualScalarWrite_transient_reencode TransientSlotControls.frame atCell.path atCell.codec atCell.slot _ atRaw atBefore rfl rfl

def atRepeat := actualScalarWrite TransientSlotControls.frame atCell.path atCell.codec atCell.slot
  (Source.intWrap unsigned16 0xabcd) atWrite.2 atWrite.1.2

theorem at_repeat_word : atRepeat.2 0=0xbeefabcd := rfl

theorem at_reset_read : (atRepeat.1.2.2.ex.endTx.transient.cells account).read atCell.path=
    some (Source.intWrap unsigned16 0) := rfl

theorem at_reset_persistent : (atRepeat.1.2.2.ex.endTx.world.accounts account).storage.read (rootPath "a")=
    some (Source.intWrap rootU8 7) := rfl

theorem at_reset_reencode : encodeScalarPath atCell.path atCell.codec atCell.slot
    (atRepeat.1.2.2.ex.endTx.transient.cells account) atRepeat.2=
      some (patchScalarSlot atRepeat.2 atCell.slot atCell.field (atCell.codec.encode (Source.intWrap unsigned16 0))) :=
  actualScalarTransient_reset TransientSlotControls.frame atCell.path atCell.codec atCell.slot _ atRepeat.2 atRepeat.1.2.2.ex rfl

theorem at_reset_word : patchScalarSlot atRepeat.2 atCell.slot atCell.field
    (atCell.codec.encode (Source.intWrap unsigned16 0)) 0=0xbeef0000 := rfl

theorem at_static : actualScalarWrite {TransientSlotControls.frame with static:=true} atCell.path atCell.codec atCell.slot
    (Source.intWrap unsigned16 0xabcd) atWrite.2 atWrite.1.2=((.error (.revert []),atWrite.1.2),atWrite.2) :=
  actualScalarWrite_static _ atCell.path atCell.codec atCell.slot _ atWrite.2 atWrite.1.2 rfl

theorem at_wrong_zero_padding : patchScalarSlot atRepeat.2 atCell.slot atCell.field
    (atCell.codec.encode (Source.intWrap unsigned16 0)) 0≠0 := by decide
end Solidity.Yul.Views.Controls
