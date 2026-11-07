import Solidity.Yul.Views.MemberDynamicSequencePrefix

-- Serialize concrete proof elaboration to bound pending computed-state memory.
set_option Elab.async false

namespace Solidity.Yul.Views.Controls
def mdZeroXRaw := saveSlot mdBoolRaw 1 0
theorem mdZeroX_ready : (mdBool.following? rfl 1 0).isSome := by
  apply mdBool.following_ready rfl
  · rw [mdBool_next]; decide
  · rw [mdBool_next]; decide
@[irreducible]
def mdZeroX : MemberOwnershipPlan packedStepFrame mdLayout mdFixed 1 0 mdBool.step.1.2 mdBool.step.2 :=
  (mdBool.following? rfl 1 0).get mdZeroX_ready
theorem mdZeroX_next : mdZeroX.nextRaw = mdZeroXRaw :=
  (congrArg (fun m => saveSlot m 1 0) (mdBool.following_raw mdZeroX rfl)).trans (congrArg (fun m => saveSlot m 1 0) mdBool_next)
theorem mdZeroX_map : finiteEncode mdZeroX.next (mdZeroX.step.1.2.2.ex.world.accounts account).storage
    (fun q => mdZeroX.step.2.cells (complementKey false account q)) = some mdZeroXRaw :=
  (mdZeroX.reencode rfl).trans (congrArg some mdZeroX_next)

def mdZeroYRaw := saveSlot mdZeroXRaw 2 0
theorem mdZeroY_ready : (mdZeroX.following? rfl 2 0).isSome := by
  apply mdZeroX.following_ready rfl
  · rw [mdZeroX_next]; decide
  · rw [mdZeroX_next]; decide
@[irreducible]
def mdZeroY : MemberOwnershipPlan packedStepFrame mdLayout mdFixed 2 0 mdZeroX.step.1.2 mdZeroX.step.2 :=
  (mdZeroX.following? rfl 2 0).get mdZeroY_ready
theorem mdZeroY_next : mdZeroY.nextRaw = mdZeroYRaw :=
  (congrArg (fun m => saveSlot m 2 0) (mdZeroX.following_raw mdZeroY rfl)).trans (congrArg (fun m => saveSlot m 2 0) mdZeroX_next)
theorem mdZeroY_map : finiteEncode mdZeroY.next (mdZeroY.step.1.2.2.ex.world.accounts account).storage
    (fun q => mdZeroY.step.2.cells (complementKey false account q)) = some mdZeroYRaw :=
  (mdZeroY.reencode rfl).trans (congrArg some mdZeroY_next)

end Solidity.Yul.Views.Controls
