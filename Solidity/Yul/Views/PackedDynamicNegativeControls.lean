import Solidity.Yul.Views.PackedDynamicFinalControls

namespace Solidity.Yul.Views.Controls

def pdCollision : Roadmap.Evm.Fixed where
  keccak _ := 0
  keccak_lt _ := by decide
  precompile _ _ := none
  precompileGas _ _ := 0

/-- Header/data collision is an unsupported checked preparation, NOT a Yul
refusal or invented execution result. No hash injectivity is postulated. -/
theorem pd_collision_none : preparePackedOwnership? packedStepFrame pdLayout pdCollision 0 1 pdState pdResidual = none := by rfl

theorem pd_noop_ready : (preparePackedOwnership? packedStepFrame pdLayout pdFixed 0 0 pdState pdResidual).isSome := by decide

@[irreducible]
def pdNoop : PackedOwnershipPlan packedStepFrame pdLayout pdFixed 0 0 pdState pdResidual :=
  (preparePackedOwnership? packedStepFrame pdLayout pdFixed 0 0 pdState pdResidual).get pd_noop_ready

theorem pd_noop_raw : pdNoop.raw = pdRaw := by
  apply pdNoop.raw_from_encoding pdRaw pd_initial_view
  exact pd_initial_encoding

theorem pd_noop_whole_store : (pdNoop.after.source.world.accounts account).storage = (pdState.2.ex.world.accounts account).storage := by
  apply pdNoop.same_word_store rfl
  exact (congrFun pd_noop_raw 0).trans (show pdRaw 0 = 0 from rfl)

theorem pd_noop_none_administration : (pdNoop.after.source.world.accounts account).storage.cell (pdPath "xs") = none := by
  rw [pd_noop_whole_store]
  rfl

theorem pd_effectful_noop_still_journals : pdNoop.after.source.journal.length = 1 := by
  unfold PackedOwnershipPlan.after
  rw [pdNoop.nonstatic rfl]
  exact Source.ExecState.journal_apply pdState.2.ex pdNoop.sourceOp

theorem pd_real_u16_hash_input (i : Nat) : (pdX.element Roadmap.Evm.withKeccak account i).slot.val =
    (Roadmap.Evm.withKeccak.keccak (layoutPreimageBytes (.data (pdX.registration account).slot.val))+i/16)%(2^256) :=
  pdX.element_word Roadmap.Evm.withKeccak account i

theorem pd_real_u24_hash_input (i : Nat) : (pdY.element Roadmap.Evm.withKeccak account i).slot.val =
    (Roadmap.Evm.withKeccak.keccak (layoutPreimageBytes (.data (pdY.registration account).slot.val))+i/10)%(2^256) :=
  pdY.element_word Roadmap.Evm.withKeccak account i

end Solidity.Yul.Views.Controls
