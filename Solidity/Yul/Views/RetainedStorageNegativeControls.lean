import Solidity.Yul.Views.RetainedRegrowControls
import Solidity.Yul.Views.RetainedClosedCaller
import Solidity.Yul.Views.RetainedOwnershipRepeat

namespace Solidity.Yul.Views.Controls

theorem rh_repeat_same_slot_map : finiteEncode rhPlan.next (rhPlan.repeatStep.1.2.2.ex.world.accounts account).storage
    (fun q => rhPlan.repeatStep.2.cells (complementKey false account q))=some rhPlan.nextRaw := rhPlan.repeat_reencode rfl

theorem rh_repeat_administrative_store : (rhPlan.repeatStep.1.2.2.ex.world.accounts account).storage=
    (rhPlan.step.1.2.2.ex.world.accounts account).storage := rhPlan.repeat_store_identity rfl

/-- One more source journal entry is real administration; store identity above
is not a claim that the WHOLE effectful execution state stayed unchanged. -/
theorem rh_repeat_real_journal : rhPlan.repeatStep.1.2.2.ex.journal.length=rhPlan.step.1.2.2.ex.journal.length+1 := by
  rw [rhPlan.repeat_nonstatic rfl]
  exact Source.ExecState.journal_apply _ _

def rhCollisionFixed : Roadmap.Evm.Fixed where
  keccak _ := 100
  keccak_lt _ := by decide
  precompile _ _ := none
  precompileGas _ _ := 0

theorem rh_collision_image_ready : (prepareRetainedArrayImage? rhLayout rhCollisionFixed rhHistory 0).isSome := by decide
def rhCollisionImage := (prepareRetainedArrayImage? rhLayout rhCollisionFixed rhHistory 0).get rh_collision_image_ready
theorem rh_collision_check : packedSeparationCheck (rhCollisionImage.snapshot rhRaw0)=false := by decide

theorem rh_source_index_failure : (Source.indexLoc (E := agEnv) packedStepFrame
    (Source.Val.storRef (τ := .array .storage (.struct .storage agNode) none) (by rfl) rhLayout.path) 2).run agApplied.2 =
      (.error (.revert (Source.panicData .index)),agApplied.2) := rhLayout.indexLoc (F := packedStepFrame) agApplied.2 2 (by rfl) 2

theorem rh_no_false_formation_here : ¬(Source.indexLoc (E := agEnv) packedStepFrame
    (Source.Val.storRef (τ := .array .storage (.struct .storage agNode) none) (by rfl) rhLayout.path) 2).run agApplied.2 =
      (.ok (.stor (rhLayout.path.go (.index 2))),agApplied.2) := by rw [rh_source_index_failure]; intro h; cases h

theorem rh_missing_root_metadata : (prepareRetainedArrayLayout? agChild "AG" account (agName "missing")).isNone=true := by decide

theorem rh_unknown_slot999 : rhRegrowRaw 999=999 := rfl

theorem rh_partial_tail_retained : rhRegrowRaw 1000=⟨77+88*65536+77*2^32+2^240,by decide⟩ := rfl

end Solidity.Yul.Views.Controls
