import Solidity.Yul.Views.MemberDynamicSequenceClear

-- Serialize concrete proof elaboration to bound pending computed-state memory.
set_option Elab.async false

namespace Solidity.Yul.Views.Controls
def mdRegrowXRaw := saveSlot mdZeroYRaw 1 18
theorem mdRegrowX_ready : (mdZeroY.following? rfl 1 18).isSome := by
  apply mdZeroY.following_ready rfl
  · rw [mdZeroY_next]; decide
  · rw [mdZeroY_next]; decide
@[irreducible]
def mdRegrowX : MemberOwnershipPlan packedStepFrame mdLayout mdFixed 1 18 mdZeroY.step.1.2 mdZeroY.step.2 :=
  (mdZeroY.following? rfl 1 18).get mdRegrowX_ready
theorem mdRegrowX_next : mdRegrowX.nextRaw = mdRegrowXRaw :=
  (congrArg (fun m => saveSlot m 1 18) (mdZeroY.following_raw mdRegrowX rfl)).trans (congrArg (fun m => saveSlot m 1 18) mdZeroY_next)
theorem mdRegrowX_map : finiteEncode mdRegrowX.next (mdRegrowX.step.1.2.2.ex.world.accounts account).storage
    (fun q => mdRegrowX.step.2.cells (complementKey false account q)) = some mdRegrowXRaw :=
  (mdRegrowX.reencode rfl).trans (congrArg some mdRegrowX_next)

def mdRegrowYRaw := saveSlot mdRegrowXRaw 2 12
theorem mdRegrowY_ready : (mdRegrowX.following? rfl 2 12).isSome := by
  apply mdRegrowX.following_ready rfl
  · rw [mdRegrowX_next]; decide
  · rw [mdRegrowX_next]; decide
@[irreducible]
def mdRegrowY : MemberOwnershipPlan packedStepFrame mdLayout mdFixed 2 12 mdRegrowX.step.1.2 mdRegrowX.step.2 :=
  (mdRegrowX.following? rfl 2 12).get mdRegrowY_ready
theorem mdRegrowY_next : mdRegrowY.nextRaw = mdRegrowYRaw :=
  (congrArg (fun m => saveSlot m 2 12) (mdRegrowX.following_raw mdRegrowY rfl)).trans (congrArg (fun m => saveSlot m 2 12) mdRegrowX_next)
theorem mdRegrowY_map : finiteEncode mdRegrowY.next (mdRegrowY.step.1.2.2.ex.world.accounts account).storage
    (fun q => mdRegrowY.step.2.cells (complementKey false account q)) = some mdRegrowYRaw :=
  (mdRegrowY.reencode rfl).trans (congrArg some mdRegrowY_next)

end Solidity.Yul.Views.Controls
