import Solidity.Yul.Views.PrimitiveDynamicControls

namespace Solidity.Yul.Views.Controls

def pcUnsignedRaw := saveSlot pcRawSigned 1 11
theorem pcunsigned_ready : (pcSigned.following? rfl 1 11).isSome := by
  apply pcSigned.following_ready rfl
  · rw [pc_signed_next]; decide
  · rw [pc_signed_next]; decide
@[irreducible]
def pcUnsigned : PrimitiveOwnershipPlan packedStepFrame pcLayout pcFixed 1 11 pcSigned.step.1.2 pcSigned.step.2 :=
  (pcSigned.following? rfl 1 11).get pcunsigned_ready

theorem pcunsigned_next : pcUnsigned.nextRaw = pcUnsignedRaw :=
  (congrArg (fun m => saveSlot m 1 11) (pcSigned.following_raw pcUnsigned rfl)).trans (congrArg (fun m => saveSlot m 1 11) pc_signed_next)

theorem pcunsigned_map : finiteEncode pcUnsigned.next (pcUnsigned.step.1.2.2.ex.world.accounts account).storage
    (fun q => pcUnsigned.step.2.cells (complementKey false account q)) = some pcUnsignedRaw :=
  (pcUnsigned.reencode rfl).trans (congrArg some pcunsigned_next)

def pcWordRaw := saveSlot pcUnsignedRaw 2 2
theorem pcword_ready : (pcUnsigned.following? rfl 2 2).isSome := by
  apply pcUnsigned.following_ready rfl
  · rw [pcunsigned_next]; decide
  · rw [pcunsigned_next]; decide
@[irreducible]
def pcWord : PrimitiveOwnershipPlan packedStepFrame pcLayout pcFixed 2 2 pcUnsigned.step.1.2 pcUnsigned.step.2 :=
  (pcUnsigned.following? rfl 2 2).get pcword_ready

theorem pcword_next : pcWord.nextRaw = pcWordRaw :=
  (congrArg (fun m => saveSlot m 2 2) (pcUnsigned.following_raw pcWord rfl)).trans (congrArg (fun m => saveSlot m 2 2) pcunsigned_next)

theorem pcword_map : finiteEncode pcWord.next (pcWord.step.1.2.2.ex.world.accounts account).storage
    (fun q => pcWord.step.2.cells (complementKey false account q)) = some pcWordRaw :=
  (pcWord.reencode rfl).trans (congrArg some pcword_next)

def pcBoolRaw := saveSlot pcWordRaw 3 3
theorem pcbool_ready : (pcWord.following? rfl 3 3).isSome := by
  apply pcWord.following_ready rfl
  · rw [pcword_next]; decide
  · rw [pcword_next]; decide
@[irreducible]
def pcBool : PrimitiveOwnershipPlan packedStepFrame pcLayout pcFixed 3 3 pcWord.step.1.2 pcWord.step.2 :=
  (pcWord.following? rfl 3 3).get pcbool_ready

theorem pcbool_next : pcBool.nextRaw = pcBoolRaw :=
  (congrArg (fun m => saveSlot m 3 3) (pcWord.following_raw pcBool rfl)).trans (congrArg (fun m => saveSlot m 3 3) pcword_next)

theorem pcbool_map : finiteEncode pcBool.next (pcBool.step.1.2.2.ex.world.accounts account).storage
    (fun q => pcBool.step.2.cells (complementKey false account q)) = some pcBoolRaw :=
  (pcBool.reencode rfl).trans (congrArg some pcbool_next)

def pcBytesPlanRaw := saveSlot pcBoolRaw 4 3
theorem pcbytesplan_ready : (pcBool.following? rfl 4 3).isSome := by
  apply pcBool.following_ready rfl
  · rw [pcbool_next]; decide
  · rw [pcbool_next]; decide
@[irreducible]
def pcBytesPlan : PrimitiveOwnershipPlan packedStepFrame pcLayout pcFixed 4 3 pcBool.step.1.2 pcBool.step.2 :=
  (pcBool.following? rfl 4 3).get pcbytesplan_ready

theorem pcbytesplan_next : pcBytesPlan.nextRaw = pcBytesPlanRaw :=
  (congrArg (fun m => saveSlot m 4 3) (pcBool.following_raw pcBytesPlan rfl)).trans (congrArg (fun m => saveSlot m 4 3) pcbool_next)

theorem pcbytesplan_map : finiteEncode pcBytesPlan.next (pcBytesPlan.step.1.2.2.ex.world.accounts account).storage
    (fun q => pcBytesPlan.step.2.cells (complementKey false account q)) = some pcBytesPlanRaw :=
  (pcBytesPlan.reencode rfl).trans (congrArg some pcbytesplan_next)

def pcAddressPlanRaw := saveSlot pcBytesPlanRaw 5 2
theorem pcaddressplan_ready : (pcBytesPlan.following? rfl 5 2).isSome := by
  apply pcBytesPlan.following_ready rfl
  · rw [pcbytesplan_next]; decide
  · rw [pcbytesplan_next]; decide
@[irreducible]
def pcAddressPlan : PrimitiveOwnershipPlan packedStepFrame pcLayout pcFixed 5 2 pcBytesPlan.step.1.2 pcBytesPlan.step.2 :=
  (pcBytesPlan.following? rfl 5 2).get pcaddressplan_ready

theorem pcaddressplan_next : pcAddressPlan.nextRaw = pcAddressPlanRaw :=
  (congrArg (fun m => saveSlot m 5 2) (pcBytesPlan.following_raw pcAddressPlan rfl)).trans (congrArg (fun m => saveSlot m 5 2) pcbytesplan_next)

theorem pcaddressplan_map : finiteEncode pcAddressPlan.next (pcAddressPlan.step.1.2.2.ex.world.accounts account).storage
    (fun q => pcAddressPlan.step.2.cells (complementKey false account q)) = some pcAddressPlanRaw :=
  (pcAddressPlan.reencode rfl).trans (congrArg some pcaddressplan_next)

def pcShrinkRaw := saveSlot pcAddressPlanRaw 0 1
theorem pcshrink_ready : (pcAddressPlan.following? rfl 0 1).isSome := by
  apply pcAddressPlan.following_ready rfl
  · rw [pcaddressplan_next]; decide
  · rw [pcaddressplan_next]; decide
@[irreducible]
def pcShrink : PrimitiveOwnershipPlan packedStepFrame pcLayout pcFixed 0 1 pcAddressPlan.step.1.2 pcAddressPlan.step.2 :=
  (pcAddressPlan.following? rfl 0 1).get pcshrink_ready

theorem pcshrink_next : pcShrink.nextRaw = pcShrinkRaw :=
  (congrArg (fun m => saveSlot m 0 1) (pcAddressPlan.following_raw pcShrink rfl)).trans (congrArg (fun m => saveSlot m 0 1) pcaddressplan_next)

theorem pcshrink_map : finiteEncode pcShrink.next (pcShrink.step.1.2.2.ex.world.accounts account).storage
    (fun q => pcShrink.step.2.cells (complementKey false account q)) = some pcShrinkRaw :=
  (pcShrink.reencode rfl).trans (congrArg some pcshrink_next)

def pcZeroRaw := saveSlot pcShrinkRaw 0 0
theorem pczero_ready : (pcShrink.following? rfl 0 0).isSome := by
  apply pcShrink.following_ready rfl
  · rw [pcshrink_next]; decide
  · rw [pcshrink_next]; decide
@[irreducible]
def pcZero : PrimitiveOwnershipPlan packedStepFrame pcLayout pcFixed 0 0 pcShrink.step.1.2 pcShrink.step.2 :=
  (pcShrink.following? rfl 0 0).get pczero_ready

theorem pczero_next : pcZero.nextRaw = pcZeroRaw :=
  (congrArg (fun m => saveSlot m 0 0) (pcShrink.following_raw pcZero rfl)).trans (congrArg (fun m => saveSlot m 0 0) pcshrink_next)

theorem pczero_map : finiteEncode pcZero.next (pcZero.step.1.2.2.ex.world.accounts account).storage
    (fun q => pcZero.step.2.cells (complementKey false account q)) = some pcZeroRaw :=
  (pcZero.reencode rfl).trans (congrArg some pczero_next)

def pcRegrowRaw := saveSlot pcZeroRaw 0 18
theorem pcregrow_ready : (pcZero.following? rfl 0 18).isSome := by
  apply pcZero.following_ready rfl
  · rw [pczero_next]; decide
  · rw [pczero_next]; decide
@[irreducible]
def pcRegrow : PrimitiveOwnershipPlan packedStepFrame pcLayout pcFixed 0 18 pcZero.step.1.2 pcZero.step.2 :=
  (pcZero.following? rfl 0 18).get pcregrow_ready

theorem pcregrow_next : pcRegrow.nextRaw = pcRegrowRaw :=
  (congrArg (fun m => saveSlot m 0 18) (pcZero.following_raw pcRegrow rfl)).trans (congrArg (fun m => saveSlot m 0 18) pczero_next)

theorem pcregrow_map : finiteEncode pcRegrow.next (pcRegrow.step.1.2.2.ex.world.accounts account).storage
    (fun q => pcRegrow.step.2.cells (complementKey false account q)) = some pcRegrowRaw :=
  (pcRegrow.reencode rfl).trans (congrArg some pcregrow_next)

end Solidity.Yul.Views.Controls
