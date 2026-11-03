import Solidity.Yul.Views.MemberDynamicReadControls
import Solidity.Yul.Views.MemberStoragePaths

namespace Solidity.Yul.Views.Controls

theorem md_computed_coverage : mdLayout.registrations.map ScalarPath.path = mdDeclarations.paths := mdLayout.coverage
theorem md_no_duplicate_paths : mdDeclarations.paths.Nodup := mdLayout.paths_unique

theorem md_wrong_member_type : checkedMemberPack (StorageDeclaration.uintArray (E := mdEnv))
    ((mdPath "box").go (.field 0)) account 0 = .error .cellMismatch := rfl

theorem md_wrong_field_index : checkedMemberPack (StorageDeclaration.uintArray (E := mdEnv))
    ((mdPath "box").go (.field 5)) account 0 = .error .cellMismatch := rfl

theorem md_nonwrapping_negative : (mdDeclarations.pack account ((2^256-1)*32)).toOption.isSome = false := by decide

def mdDuplicateDeclarations : RootMemberDeclarations mdEnv [(mdName "top",.array .storage .bool none),(mdName "top",.array .storage .bool none)] :=
  .cons (.leaf (.scalarArray .bool)) (.cons (.leaf (.scalarArray .bool)) .nil)
theorem md_duplicate_metadata : (prepareMemberComputedStorage mdDuplicateDeclarations "ND" account).toOption.isSome = false := by decide

def mdMissingDeclarations : RootMemberDeclarations mdEnv [(mdName "top",.array .storage .bool none)] := .cons (.leaf (.scalarArray .bool)) .nil
theorem md_missing_metadata : (prepareMemberComputedStorage mdMissingDeclarations "ND" account).toOption.isSome = false := by decide

def mdCollisionFixed : Roadmap.Evm.Fixed where
  keccak _ := 0
  keccak_lt _ := by decide
  precompile _ _ := none
  precompileGas _ _ := 0
theorem md_real_overlap_rejected : packedSeparationCheck (mdLayout.snapshot mdCollisionFixed (saveSlot mdRaw 1 17)) = false := by decide

/-- Explicit raw write to a byte OUTSIDE current live length three. It succeeds
and remains residual; only the subsequent canonical growth exposes bool byte2.
The older seed had byte1 there, so that earlier negative claim was false. -/
def mdDirtyWord : Roadmap.Word := ⟨2^248+2*2^24+2^16+1,by decide⟩
def mdDirtyRaw := saveSlot mdRegrowYRaw 3000 mdDirtyWord
theorem mdDirty_ready : (mdRegrowY.following? rfl 3000 mdDirtyWord).isSome := by
  apply mdRegrowY.following_ready rfl
  · rw [mdRegrowY_next]; decide
  · rw [mdRegrowY_next]; decide
@[irreducible]
def mdDirty : MemberOwnershipPlan packedStepFrame mdLayout mdFixed 3000 mdDirtyWord mdRegrowY.step.1.2 mdRegrowY.step.2 :=
  (mdRegrowY.following? rfl 3000 mdDirtyWord).get mdDirty_ready
theorem mdDirty_next : mdDirty.nextRaw = mdDirtyRaw :=
  (congrArg (fun m => saveSlot m 3000 mdDirtyWord) (mdRegrowY.following_raw mdDirty rfl)).trans
    (congrArg (fun m => saveSlot m 3000 mdDirtyWord) mdRegrowY_next)
theorem mdDirty_map : finiteEncode mdDirty.next (mdDirty.step.1.2.2.ex.world.accounts account).storage
    (fun q => mdDirty.step.2.cells (complementKey false account q)) = some mdDirtyRaw :=
  (mdDirty.reencode rfl).trans (congrArg some mdDirty_next)

theorem md_dirty_canonical_false : (finiteAccountWrite? (T := mdEnv.lay) account
    (mdLayout.snapshot mdFixed (saveSlot mdDirtyRaw 4 4)) (saveSlot mdDirtyRaw 4 4)).isSome = false := by decide

theorem md_dirty_canonical_none : finiteAccountWrite? (T := mdEnv.lay) account
    (mdLayout.snapshot mdFixed (saveSlot mdDirtyRaw 4 4)) (saveSlot mdDirtyRaw 4 4) = none := by
  cases found : finiteAccountWrite? (T := mdEnv.lay) account (mdLayout.snapshot mdFixed (saveSlot mdDirtyRaw 4 4)) (saveSlot mdDirtyRaw 4 4) with
  | none => rfl
  | some op => have bad := md_dirty_canonical_false; rw [found] at bad; cases bad

theorem md_dirty_prefix_none : mdDirty.following? rfl 4 4 = none := by
  unfold MemberOwnershipPlan.following?
  split
  · have bad : finiteAccountWrite? (T := mdEnv.lay) account (mdLayout.snapshot mdFixed (saveSlot mdDirty.nextRaw 4 4)) (saveSlot mdDirty.nextRaw 4 4) = none := by
      rw [mdDirty_next]
      exact md_dirty_canonical_none
    dsimp only
    split
    · rfl
    · rename_i op found
      have impossible : none = some op := bad.symm.trans found
      cases impossible
  · rfl

theorem md_dirty_fresh_none : prepareMemberOwnership? packedStepFrame mdLayout mdFixed 4 4 mdDirty.step.1.2 mdDirty.step.2 = none :=
  (mdDirty.following_fresh rfl 4 4).symm.trans md_dirty_prefix_none

theorem md_late_unsupported_prefix : runMemberOwnership? packedStepFrame mdLayout mdFixed [(3000,mdDirtyWord),(4,4)] mdRegrowY.step.1.2 mdRegrowY.step.2 =
    (none,mdDirty.step.1.2,mdDirty.step.2) := mdDirty.batch_late_unsupported 4 4 [] rfl md_dirty_fresh_none

/-- Enclosing padding remains residual; no owned dirty bits are relabelled. -/
theorem md_enclosing_padding : lowByte (mdRegrowY.step.2.cells (complementKey false account 0)) ⟨30,by decide⟩ = 1 := by
  have same := mdRegrowY.residual_byte rfl 0 ⟨30,by decide⟩ (by rw [show mdRegrowY.next = mdLayout.snapshot mdFixed mdRegrowY.nextRaw from rfl,mdRegrowY_next]; decide)
  rw [mdRegrowY_next] at same
  exact same

theorem md_other_account (b : Roadmap.Address) (different : b ≠ account) :
    mdRegrowY.after.source.world.accounts b = mdRegrowX.step.1.2.2.ex.world.accounts b := mdRegrowY.account_other b different

theorem md_no_transient_claim : mdRegrowY.after.source.transient = mdRegrowX.step.1.2.2.ex.transient := mdRegrowY.transient_unchanged

end Solidity.Yul.Views.Controls
