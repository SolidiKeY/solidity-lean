import Solidity.Yul.Views.SignedDynamicFinalControls

namespace Solidity.Yul.Views.Controls

def sdCollision : Roadmap.Evm.Fixed where
  keccak _ := 0
  keccak_lt _ := by decide
  precompile _ _ := none
  precompileGas _ _ := 0

/-- Header/data collision is an unsupported checked preparation, NOT a Yul
refusal or invented execution result. No hash injectivity is postulated. -/
theorem sd_collision_none : prepareIntOwnership? packedStepFrame sdLayout sdCollision 0 1 sdState sdResidual = none := by rfl

theorem sd_noop_ready : (prepareIntOwnership? packedStepFrame sdLayout sdFixed 0 0 sdState sdResidual).isSome := by decide

@[irreducible]
def sdNoop : IntOwnershipPlan packedStepFrame sdLayout sdFixed 0 0 sdState sdResidual :=
  (prepareIntOwnership? packedStepFrame sdLayout sdFixed 0 0 sdState sdResidual).get sd_noop_ready

theorem sd_noop_raw : sdNoop.raw = sdRaw := by
  apply sdNoop.raw_from_encoding sdRaw sd_initial_view
  exact sd_initial_encoding

theorem sd_noop_whole_store : (sdNoop.after.source.world.accounts account).storage = (sdState.2.ex.world.accounts account).storage := by
  apply sdNoop.same_word_store rfl
  exact (congrFun sd_noop_raw 0).trans (show sdRaw 0 = 0 from rfl)

theorem sd_noop_none_administration : (sdNoop.after.source.world.accounts account).storage.cell (sdPath "xs") = none := by
  rw [sd_noop_whole_store]
  rfl

theorem sd_effectful_noop_still_journals : sdNoop.after.source.journal.length = 1 := by
  unfold IntOwnershipPlan.after
  rw [sdNoop.nonstatic rfl]
  exact Source.ExecState.journal_apply sdState.2.ex sdNoop.sourceOp

theorem sd_real_i16_hash_input (i : Nat) : (sdX.element Roadmap.Evm.withKeccak account i).slot.val =
    (Roadmap.Evm.withKeccak.keccak (layoutPreimageBytes (.data (sdX.registration account).slot.val))+i/16)%(2^256) :=
  sdX.element_word Roadmap.Evm.withKeccak account i

theorem sd_real_i24_hash_input (i : Nat) : (sdY.element Roadmap.Evm.withKeccak account i).slot.val =
    (Roadmap.Evm.withKeccak.keccak (layoutPreimageBytes (.data (sdY.registration account).slot.val))+i/10)%(2^256) :=
  sdY.element_word Roadmap.Evm.withKeccak account i

end Solidity.Yul.Views.Controls
