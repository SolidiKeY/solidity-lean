import Solidity.Yul.Views.MemberDynamicControls

-- Serialize concrete proof elaboration to bound pending computed-state memory.
set_option Elab.async false

namespace Solidity.Yul.Views.Controls

def mdSignedRaw := saveSlot mdGrowRaw 2 11
theorem mdSigned_ready : (mdGrow.following? rfl 2 11).isSome := by
  apply mdGrow.following_ready rfl
  · rw [md_grow_next]; decide
  · rw [md_grow_next]; decide
@[irreducible]
def mdSigned : MemberOwnershipPlan packedStepFrame mdLayout mdFixed 2 11 mdGrow.step.1.2 mdGrow.step.2 :=
  (mdGrow.following? rfl 2 11).get mdSigned_ready
theorem mdSigned_next : mdSigned.nextRaw = mdSignedRaw :=
  (congrArg (fun m => saveSlot m 2 11) (mdGrow.following_raw mdSigned rfl)).trans (congrArg (fun m => saveSlot m 2 11) md_grow_next)
theorem mdSigned_map : finiteEncode mdSigned.next (mdSigned.step.1.2.2.ex.world.accounts account).storage
    (fun q => mdSigned.step.2.cells (complementKey false account q)) = some mdSignedRaw :=
  (mdSigned.reencode rfl).trans (congrArg some mdSigned_next)

def mdBoolRaw := saveSlot mdSignedRaw 4 3
theorem mdBool_ready : (mdSigned.following? rfl 4 3).isSome := by
  apply mdSigned.following_ready rfl
  · rw [mdSigned_next]; decide
  · rw [mdSigned_next]; decide
@[irreducible]
def mdBool : MemberOwnershipPlan packedStepFrame mdLayout mdFixed 4 3 mdSigned.step.1.2 mdSigned.step.2 :=
  (mdSigned.following? rfl 4 3).get mdBool_ready
theorem mdBool_next : mdBool.nextRaw = mdBoolRaw :=
  (congrArg (fun m => saveSlot m 4 3) (mdSigned.following_raw mdBool rfl)).trans (congrArg (fun m => saveSlot m 4 3) mdSigned_next)
theorem mdBool_map : finiteEncode mdBool.next (mdBool.step.1.2.2.ex.world.accounts account).storage
    (fun q => mdBool.step.2.cells (complementKey false account q)) = some mdBoolRaw :=
  (mdBool.reencode rfl).trans (congrArg some mdBool_next)

end Solidity.Yul.Views.Controls
