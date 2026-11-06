import Solidity.Yul.Views.OwnedBoolFrame
import Solidity.Yul.Views.PackedResidualTypedSourceControls
import Solidity.Yul.Views.LayoutOriginControls

namespace Solidity.Yul.Views.Controls

/-- Noncanonical bytes remain inside the OWNED field. Padding is independent. -/
def dirtyBoolRaw : Roadmap.Word := ⟨0xabcdef000002,by decide⟩
def dirtyBoolRequest : PackedSlotRequest := ⟨false,account,7,dirtyBoolRaw⟩
def dirtyBoolPrepared := prepareRepresentedSlot packedTypedRegistry packedTypedRegistry dirtyBoolRequest boolEncodingInitial
theorem dirty_bool_prepares : dirtyBoolPrepared.isSome := by decide
def dirtyBoolPlan := dirtyBoolPrepared.get dirty_bool_prepares
def dirtyBoolRun := representedSourceStep packedTypedRegistry packedTypedRegistry dirtyBoolRequest boolEncodingInitial
  packedStepFrame dirtyBoolPlan packedTypedState packedTypedResidual

theorem dirty_bool_source_truth : (dirtyBoolRun.1.1.2.2.ex.world.accounts account).storage.read finiteFlag=some (.bool true) := rfl
theorem dirty_bool_exact_raw :
    reencodePersistentSlot (representedBanks packedTypedRegistry false dirtyBoolRun.2)
      ⟨dirtyBoolRun.1.1.2.2.ex,dirtyBoolRun.1.2⟩ account 7=some dirtyBoolRaw :=
  represented_step_persistent_at_request packedStepFrame dirtyBoolPlan packedTypedState packedTypedResidual rfl rfl
    ((packedSeparationCheck_iff _).mp (by decide))
theorem dirty_bool_representation_two : dirtyBoolRun.2.cells (ownedByteKey false account packedTypedFlag)=⟨⟨2,by decide⟩,by decide⟩ := rfl
theorem dirty_bool_old_canonical_refuses : (boolCodec packedTypedEnv.layout).decode ⟨2,by decide⟩=none := rfl

def dirtyBoolThreeRequest : PackedSlotRequest := ⟨false,account,7,⟨0xabcdef000003,by decide⟩⟩
def dirtyBoolThreePrepared := prepareRepresentedSlot packedTypedRegistry packedTypedRegistry dirtyBoolThreeRequest dirtyBoolRun.2
theorem dirty_bool_three_prepares : dirtyBoolThreePrepared.isSome := by decide
def dirtyBoolThreePlan := dirtyBoolThreePrepared.get dirty_bool_three_prepares
def dirtyBoolThreeRun := representedSourceStep packedTypedRegistry packedTypedRegistry dirtyBoolThreeRequest dirtyBoolRun.2
  packedStepFrame dirtyBoolThreePlan dirtyBoolRun.1.1.2 dirtyBoolRun.1.2

theorem dirty_bool_same_truth_admin_identity :
    (dirtyBoolThreeRun.1.1.2.2.ex.world.accounts account).storage=(dirtyBoolRun.1.1.2.2.ex.world.accounts account).storage := rfl

theorem dirty_bool_three_raw :
    reencodePersistentSlot (representedBanks packedTypedRegistry false dirtyBoolThreeRun.2)
      ⟨dirtyBoolThreeRun.1.1.2.2.ex,dirtyBoolThreeRun.1.2⟩ account 7=some dirtyBoolThreeRequest.raw :=
  represented_step_persistent_at_request packedStepFrame dirtyBoolThreePlan dirtyBoolRun.1.1.2 dirtyBoolRun.1.2 rfl rfl
    ((packedSeparationCheck_iff _).mp (by decide))

theorem dirty_bool_static_preserves_caller :
    representedSourceStep packedTypedRegistry packedTypedRegistry dirtyBoolThreeRequest dirtyBoolRun.2
      {packedStepFrame with static:=true} dirtyBoolThreePlan dirtyBoolRun.1.1.2 dirtyBoolRun.1.2=
    (((.error (.revert []),dirtyBoolRun.1.1.2),dirtyBoolRun.1.2),dirtyBoolRun.2) := representedSourceStep_static _ _ _ _ rfl

theorem dirty_bool_child_rollback :
    companionRollback (companionEnter ⟨dirtyBoolRun.1.1.2.2.ex,dirtyBoolRun.1.2⟩ account account 0 [] false)
      ⟨dirtyBoolThreeRun.1.1.2.2.ex,dirtyBoolThreeRun.1.2⟩=⟨dirtyBoolRun.1.1.2.2.ex,dirtyBoolRun.1.2⟩ ∧
    boolEncodingRollback dirtyBoolRun.2.journal.length dirtyBoolThreeRun.2=dirtyBoolRun.2 :=
  represented_step_rollback packedStepFrame dirtyBoolThreePlan dirtyBoolRun.1.1.2 dirtyBoolRun.1.2 rfl

theorem dirty_bool_every_H (H : Source.HeapTy) (ok : Source.MemOK packedTypedEnv H packedTypedState) :
    Source.MemOK packedTypedEnv H dirtyBoolRun.1.1.2 := representedSourceStep_MemOK H _ _ _ _ ok

theorem dirty_bool_other_account_code : dirtyBoolRun.2.cells (ownedByteKey false ⟨account.val+1,by decide⟩ packedTypedFlag)=canonicalTrueByte := rfl
theorem dirty_bool_other_bank_code : dirtyBoolRun.2.cells (ownedByteKey true account packedTypedFlag)=canonicalTrueByte := rfl

theorem dirty_bool_mismatched_request_rejected : dirtyBoolPlan.packed.request≠dirtyBoolThreeRequest := by
  intro same
  have raw := congrArg (fun q : PackedSlotRequest => q.raw.val) same
  have different : dirtyBoolPlan.packed.request.raw.val≠dirtyBoolThreeRequest.raw.val := by decide
  exact different raw

/-- This wrapper is computed from the real inherited declarations/layout-at42;
the path/coordinate planner and canonical narrow codecs are not replaced. -/
theorem dirty_bool_actual_declared_separation : finiteSeparated (originChecked.represented boolEncodingInitial) := originChecked.represented_separated _
theorem dirty_bool_actual_declared_coverage : (originChecked.represented boolEncodingInitial).map ScalarPath.path=originDeclarations.paths := originChecked.represented_paths _

theorem dirty_bool_transaction_banks :
    (boolEncodingEndTx dirtyBoolThreeRun.2).cells (ownedByteKey false account packedTypedFlag)=⟨⟨3,by decide⟩,by decide⟩ ∧
    (boolEncodingEndTx dirtyBoolThreeRun.2).cells (ownedByteKey true account packedTypedFlag)=canonicalTrueByte := ⟨rfl,rfl⟩

/-- Pure view preparation does not manufacture explicit default cells. -/
def dirtyBoolEmptyStore : Source.Storage packedTypedEnv.layout (packedTypedEnv.lay account) := .empty

theorem dirty_bool_empty_view : finiteView (representedRegistry (packedTypedRegistry account) false account boolEncodingInitial)
    dirtyBoolEmptyStore (fun _ => 0) := by
  intro c member
  simp only [representedRegistry,packedTypedRegistry,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem dirty_bool_empty_admin :
    representedStoreWriteback (packedTypedRegistry account) false account (fun _ => 0) boolEncodingInitial dirtyBoolEmptyStore=
    some ((dirtyBoolEmptyStore,packedMask (packedTypedRegistry account) (fun _ => 0)),boolEncodingInitial) :=
  representedStoreWriteback_unchanged _ _ _ _ _ _ dirty_bool_empty_view

/-- The old canonical API still refuses2. The new codec covers every physical
byte with a derived nonzero choice and proves exact inversion, not cleanup. -/
theorem dirty_bool_all_bytes (raw : Fin 256) :
    (representedBoolCodec packedTypedEnv.layout boolField rfl (chooseTrueByte canonicalTrueByte raw)).decode
      ⟨raw.val,by have h:=raw.isLt; simpa only [boolField] using h⟩=some (.bool (boolByteMeaning raw)) := by
  simpa only [boolField,fieldBooleanByte] using representedBool_decode_raw packedTypedEnv.layout boolField rfl canonicalTrueByte
    (⟨raw.val,by have h:=raw.isLt; simpa only [boolField] using h⟩)

theorem dirty_bool_actual_source_outer_rollback :
    companionRollback (companionEnter ⟨packedTypedState.2.ex,packedTypedResidual⟩ account account 0 [] false)
      (companionCommit (companionEnter ⟨dirtyBoolRun.1.1.2.2.ex,dirtyBoolRun.1.2⟩ account account 0 [] false)
        ⟨dirtyBoolThreeRun.1.1.2.2.ex,dirtyBoolThreeRun.1.2⟩)=⟨packedTypedState.2.ex,packedTypedResidual⟩ ∧
    boolEncodingRollback boolEncodingInitial.journal.length dirtyBoolThreeRun.2=boolEncodingInitial :=
  represented_two_outer_rollback packedStepFrame dirtyBoolPlan packedTypedState packedTypedResidual dirtyBoolThreeRequest dirtyBoolThreePlan rfl

end Solidity.Yul.Views.Controls
