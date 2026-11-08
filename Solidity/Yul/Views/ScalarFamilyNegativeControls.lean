import Solidity.Yul.Views.ScalarFamilyMixedControls
import Solidity.Yul.Views.GenericFlow.FollowingLaws

namespace Solidity.Yul.Views.Controls

def sfCollision : Roadmap.Evm.Fixed where
  keccak _ := 0
  keccak_lt _ := by decide
  precompile _ _ := none
  precompileGas _ _ := 0

/-- Header/data collision is an unsupported checked preparation, NOT a Yul
refusal or invented execution result. No hash injectivity is postulated. -/
theorem sf_collision_none : prepareScalarOwnership? packedStepFrame sfLayout sfCollision 0 1 sfState sfResidual = none := by rfl

theorem sf_noop_ready : (prepareScalarOwnership? packedStepFrame sfLayout sfFixed 0 0 sfState sfResidual).isSome := by decide

@[irreducible]
def sfNoop : ScalarOwnershipPlan packedStepFrame sfLayout sfFixed 0 0 sfState sfResidual :=
  (prepareScalarOwnership? packedStepFrame sfLayout sfFixed 0 0 sfState sfResidual).get sf_noop_ready

theorem sf_noop_raw : sfNoop.raw = sfRaw := by
  apply sfNoop.raw_from_encoding sfRaw sf_initial_view
  exact sf_initial_encoding

theorem sf_noop_whole_store : (sfNoop.after.source.world.accounts account).storage = (sfState.2.ex.world.accounts account).storage := by
  apply sfNoop.same_word_store rfl
  exact (congrFun sf_noop_raw 0).trans (show sfRaw 0 = 0 from rfl)

theorem sf_noop_none_administration : (sfNoop.after.source.world.accounts account).storage.cell (sfPath "xs") = none := by
  rw [sf_noop_whole_store]
  rfl

theorem sf_effectful_noop_still_journals : sfNoop.after.source.journal.length = 1 := by
  unfold ScalarOwnershipPlan.after
  rw [sfNoop.nonstatic rfl]
  exact Source.ExecState.journal_apply sfState.2.ex sfNoop.sourceOp

theorem sf_real_bool_hash_input (i : Nat) : (sfX.element Roadmap.Evm.withKeccak account i).slot.val =
    (Roadmap.Evm.withKeccak.keccak (layoutPreimageBytes (.data (sfX.registration account).slot.val))+i/32)%(2^256) := sfX.element_word Roadmap.Evm.withKeccak account i

theorem sf_real_bytes_hash_input (i : Nat) : (sfY.element Roadmap.Evm.withKeccak account i).slot.val =
    (Roadmap.Evm.withKeccak.keccak (layoutPreimageBytes (.data (sfY.registration account).slot.val))+i/10)%(2^256) := sfY.element_word Roadmap.Evm.withKeccak account i

theorem sf_real_address_hash_input (i : Nat) : (sfZ.element Roadmap.Evm.withKeccak account i).slot.val =
    (Roadmap.Evm.withKeccak.keccak (layoutPreimageBytes (.data (sfZ.registration account).slot.val))+i)%(2^256) := by
  simpa only [show sfZ.perSlot = 1 from rfl,Nat.div_one] using sfZ.element_word Roadmap.Evm.withKeccak account i

/-- This previously residual raw bool byte2 is NOT canonical source bool. None
is unsupported PREPARATION; the independent EVM dirtyGrow succeeds. -/
theorem sf_dirty_growth_decode_none : (finiteAccountWrite? (T := sfEnv.lay) account
    (sfLayout.scalarFamilySnapshot sfFixed (saveSlot sfMixedRaw 0 35)) (saveSlot sfMixedRaw 0 35)) = none := by
  have bad : (finiteAccountWrite? (T := sfEnv.lay) account (sfLayout.scalarFamilySnapshot sfFixed (saveSlot sfMixedRaw 0 35)) (saveSlot sfMixedRaw 0 35)).isSome = false := by decide
  cases found : finiteAccountWrite? (T := sfEnv.lay) account (sfLayout.scalarFamilySnapshot sfFixed (saveSlot sfMixedRaw 0 35)) (saveSlot sfMixedRaw 0 35) with
  | none => rfl
  | some op => rw [found] at bad; cases bad

theorem sf_dirty_growth_preparation_none : sfZFill.following? rfl 0 35 = none := by
  have bad : finiteAccountWrite? (T := sfEnv.lay) account (sfLayout.scalarFamilySnapshot sfFixed (saveSlot sfZFill.nextRaw 0 35)) (saveSlot sfZFill.nextRaw 0 35) = none := by
    rw [sfzfill_next]
    exact sf_dirty_growth_decode_none
  unfold ScalarOwnershipPlan.following?
  exact GenericFlow.Following.none_of_write_none _ bad

theorem sf_dirty_growth_fresh_none : prepareScalarOwnership? packedStepFrame sfLayout sfFixed 0 35 sfZFill.step.1.2 sfZFill.step.2 = none :=
  (sfZFill.following_fresh rfl 0 35).symm.trans sf_dirty_growth_preparation_none

def sfWrongDeclarations : StorageDeclarations sfEnv
    [(sfName "xs",Source.STy.array .storage sfBytes.ty none),(sfName "marker",.int .u256),
     (sfName "ys",.array .storage sfBytes.ty none),(sfName "zs",.array .storage sfAddress.ty none)] :=
  .cons (.scalarArray sfBytes) (.cons (.fixed (.scalar (.int .u256) rfl))
    (.cons (.scalarArray sfBytes) (.cons (.scalarArray sfAddress) .nil)))

theorem sf_checked_wrong_element_type : (prepareComputedStorage sfWrongDeclarations "SF" account).toOption.isSome = false := by decide

def sfMissingDeclarations : StorageDeclarations sfEnv [(sfName "xs",.array .storage .bool none)] := .cons (.scalarArray .bool) .nil

theorem sf_checked_missing_roots : (prepareComputedStorage sfMissingDeclarations "SF" account).toOption.isSome = false := by decide

end Solidity.Yul.Views.Controls
