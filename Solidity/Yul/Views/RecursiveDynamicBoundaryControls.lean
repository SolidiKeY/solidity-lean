import Solidity.Yul.Views.RecursiveDynamicReadControls
import Solidity.Yul.Views.RecursiveRootLegacy

namespace Solidity.Yul.Views.Controls

theorem rc_exact_coverage : rcLayout.registrations.map ScalarPath.path = rcDeclarations.paths := rcLayout.coverage
theorem rc_no_duplicate_paths : rcDeclarations.paths.Nodup := rcLayout.paths_unique
theorem rc_exact_end : rcLayout.endByte = 256 := rfl

theorem rc_truncated_member : checkedRecursivePack (RecursiveStorageDeclaration.leaf
    (StorageDeclaration.packedUnsignedArray (E := rcEnv) rcU16 rfl (by decide)))
    ⟨rcName "box",[.field 1,.field 1]⟩ account 64 = .error .cellMismatch := rfl

theorem rc_wrong_member : checkedRecursivePack (RecursiveStorageDeclaration.leaf
    (StorageDeclaration.packedUnsignedArray (E := rcEnv) rcU16 rfl (by decide)))
    ⟨rcName "box",[.field 1,.field 0]⟩ account 64 = .error .cellMismatch := rfl

theorem rc_missing_member : checkedRecursivePack (RecursiveStorageDeclaration.leaf
    (StorageDeclaration.packedUnsignedArray (E := rcEnv) rcU16 rfl (by decide)))
    ⟨rcName "box",[.field 1,.field 1,.field 3]⟩ account 64 = .error .cellMismatch := rfl

theorem rc_overflow : (rcDeclarations.pack account ((2^256-1)*32)).toOption.isSome = false := by decide

def rcMissingDeclarations : RecursiveRootDeclarations rcEnv [(rcName "marker",.int .u256)] := .cons (.leaf (.fixed (.scalar (.int .u256) rfl))) .nil
theorem rc_missing_metadata : (prepareRecursiveComputedStorage rcMissingDeclarations "RC" account).toOption.isSome = false := by decide

def rcDuplicateDeclarations : RecursiveRootDeclarations rcEnv [(rcName "box",.struct .storage (rcTypeName "OuterR")),(rcName "box",.struct .storage (rcTypeName "OuterR")),(rcName "marker",.int .u256)] :=
  .cons rcOuter (.cons rcOuter (.cons (.leaf (.fixed (.scalar (.int .u256) rfl))) .nil))
theorem rc_duplicate_metadata : (prepareRecursiveComputedStorage rcDuplicateDeclarations "RC" account).toOption.isSome = false := by decide

def rcCollision : Roadmap.Evm.Fixed where
  keccak _ := 0
  keccak_lt _ := by decide
  precompile _ _ := none
  precompileGas _ _ := 0

theorem rc_overlap_rejected : packedSeparationCheck (rcLayout.snapshot rcCollision (saveSlot rcRaw 2 17)) = false := by decide

theorem rc_duplicated_coverage : packedSeparationCheck (rcLayout.registrations ++ rcLayout.registrations) = false := by decide

theorem rc_dirty_false : (finiteAccountWrite? (T := rcEnv.lay) account
    (rcLayout.snapshot rcFixed (saveSlot rcRegrowYRaw 5 4)) (saveSlot rcRegrowYRaw 5 4)).isSome = false := by decide

theorem rc_dirty_none : finiteAccountWrite? (T := rcEnv.lay) account
    (rcLayout.snapshot rcFixed (saveSlot rcRegrowYRaw 5 4)) (saveSlot rcRegrowYRaw 5 4) = none := by
  cases found : finiteAccountWrite? (T := rcEnv.lay) account (rcLayout.snapshot rcFixed (saveSlot rcRegrowYRaw 5 4)) (saveSlot rcRegrowYRaw 5 4) with
  | none => rfl
  | some op => have bad := rc_dirty_false; rw [found] at bad; cases bad

theorem rc_dirty_following : rcRegrowY.following? rfl 5 4 = none := by
  unfold RecursiveOwnershipPlan.following?
  split
  · have bad : finiteAccountWrite? (T := rcEnv.lay) account (rcLayout.snapshot rcFixed (saveSlot rcRegrowY.nextRaw 5 4)) (saveSlot rcRegrowY.nextRaw 5 4) = none := by
      rw [rcRegrowY_next]
      exact rc_dirty_none
    dsimp only
    split
    · rfl
    · rename_i op found
      have impossible : none = some op := bad.symm.trans found
      cases impossible
  · rfl

theorem rc_dirty_fresh : prepareRecursiveOwnership? packedStepFrame rcLayout rcFixed 5 4 rcRegrowY.step.1.2 rcRegrowY.step.2 = none :=
  (rcRegrowY.following_fresh rfl 5 4).symm.trans rc_dirty_following

theorem rc_unsupported_late_prefix : runRecursiveOwnership? packedStepFrame rcLayout rcFixed [(3,12),(5,4)] rcRegrowX.step.1.2 rcRegrowX.step.2 =
    (none,rcRegrowY.step.1.2,rcRegrowY.step.2) := rcRegrowY.batch_late_unsupported 5 4 [] rfl rc_dirty_fresh

theorem rc_inner_tail_padding : lowByte (rcRegrowY.step.2.cells (complementKey false account 4)) ⟨31,by decide⟩ = 1 := by
  have same := rcRegrowY.residual_byte rfl 4 ⟨31,by decide⟩ (by rw [show rcRegrowY.next = rcLayout.snapshot rcFixed rcRegrowY.nextRaw from rfl,rcRegrowY_next]; decide)
  rw [rcRegrowY_next] at same
  exact same

theorem rc_other_account (b : Roadmap.Address) (different : b ≠ account) :
    rcRegrowY.after.source.world.accounts b = rcRegrowX.step.1.2.2.ex.world.accounts b := rcRegrowY.account_other b different

theorem rc_transient_unchanged : rcRegrowY.after.source.transient = rcRegrowX.step.1.2.2.ex.transient := rcRegrowY.transient_unchanged

theorem rc_unsigned_32768 :
    (Source.readLoc (E := rcEnv) packedStepFrame (Source.Loc.stor (τ := .int rcU16) (rcX.elementPath 17))).run rcRegrowY.step.1.2 =
      (.ok (.int 32768 (by decide)),rcRegrowY.step.1.2) := rc_x_read 17 (by decide)

theorem rc_signed_minimum :
    (Source.readLoc (E := rcEnv) packedStepFrame (Source.Loc.stor (τ := .int rcI24) (rcY.elementPath 11))).run rcRegrowY.step.1.2 =
      (.ok (.int (-8388608) (by decide)),rcRegrowY.step.1.2) := rc_y_read 11 (by decide)

end Solidity.Yul.Views.Controls
