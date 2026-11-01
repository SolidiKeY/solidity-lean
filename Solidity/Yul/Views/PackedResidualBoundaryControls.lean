import Solidity.Yul.Views.PackedResidualControls
import Solidity.Source.WellTyped

namespace Solidity.Yul.Views.Controls

def packedZeroRequest : PackedSlotRequest := ⟨false,account,7,packedZeroRaw⟩
theorem packed_zero_plan_exists : (preparePackedSlot packedRegistry packedRegistry packedZeroRequest).isSome := by decide
def packedZeroPlan := (preparePackedSlot packedRegistry packedRegistry packedZeroRequest).get packed_zero_plan_exists

theorem packed_zero_original_view : finiteView (selectedSlotPaths packedPaths 7) packedInitialStore (fun _ => packedZeroRaw) := by
  intro c member
  change c ∈ [packedFlag,packedSmall,packedBytes,packedAddress] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem packed_unchanged_whole_companion : packedStateWriteback packedRegistry packedRegistry packedInitial packedZeroRequest = some packedInitial :=
  packedStateWriteback_identity packedInitial packedZeroRequest packedZeroPlan (Option.some_get packed_zero_plan_exists).symm packed_zero_original_view rfl

def packedExplicitStore := (((packedInitialStore.write finiteFlag (.bool false)).write finiteSmall (.int 0 (by decide))).write packedBytesPath (.fixedBytes [0,0,0] rfl)).write packedAddressPath (.address 0)
def packedExplicitSource : Source.ExecState layout packedPerAccount packedPerAccount :=
  ⟨⟨fun _ => {Source.Account.empty (D := layout) packedLayout with storage := packedExplicitStore}⟩,.empty,[]⟩
def packedExplicit : ResidualCompanion layout packedPerAccount packedPerAccount complementCarrierOwnership := ⟨packedExplicitSource,packedInitial.residual⟩

theorem packed_explicit_original_view : finiteView (selectedSlotPaths packedPaths 7) packedExplicitStore (fun _ => packedZeroRaw) := by
  intro c member
  change c ∈ [packedFlag,packedSmall,packedBytes,packedAddress] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem packed_unchanged_admin_distinction :
    packedStateWriteback packedRegistry packedRegistry packedExplicit packedZeroRequest = some packedExplicit ∧
    packedInitialStore.cell finiteFlag = none ∧ packedExplicitStore.cell finiteFlag = some (.bool false) :=
  ⟨packedStateWriteback_identity packedExplicit packedZeroRequest packedZeroPlan (Option.some_get packed_zero_plan_exists).symm packed_explicit_original_view rfl,rfl,rfl⟩

theorem packed_reset_zero_defaults (c : ScalarPath layout packedLayout) (member : c ∈ selectedSlotPaths packedPaths 7) :
    ∃ v, Source.Val.default layout (packedLayout c.path) = some v ∧ (c.codec.encode v).val = 0 := by
  change c ∈ [packedFlag,packedSmall,packedBytes,packedAddress] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨.bool false,rfl,rfl⟩
  · exact ⟨.int 0 (by decide),rfl,rfl⟩
  · exact ⟨.fixedBytes [0,0,0] rfl,rfl,rfl⟩
  · exact ⟨.address 0,rfl,rfl⟩

theorem packed_transaction_complete_words :
    reencodePersistentSlot packedRegistry (companionEndTx packedChild) account 7 = some packedRawB ∧
    reencodeTransientSlot packedRegistry (companionEndTx packedChild) account 7 = some 0 ∧
    (companionEndTx packedChild).source.journal = [] ∧ (companionEndTx packedChild).residual.journal = [] :=
  ⟨(packedEndTx_persistent _ _ _ _).trans packed_full_raw_child.1,packedEndTx_transient _ _ _ _ packed_reset_zero_defaults,rfl,rfl⟩

theorem packed_transaction_fields :
    ((companionEndTx packedChild).source.world.accounts account).storage.read finiteSmall = some (.int 0xbeef (by decide)) ∧
    ((companionEndTx packedChild).source.transient.cells account).cell finiteSmall = none ∧
    ((companionEndTx packedChild).source.transient.cells account).read finiteSmall = some (.int 0 (by decide)) := ⟨rfl,rfl,rfl⟩

def packedMalformed : PackedSlotRequest := ⟨false,account,7,packedFlag.field.saveWord packedRawA ⟨2,by decide⟩⟩
theorem packed_invalid_no_plan : preparePackedSlot packedRegistry packedRegistry packedMalformed = none ∧
    packedStateWriteback packedRegistry packedRegistry packedInitial packedMalformed = none := ⟨rfl,rfl⟩

def packedOverlap := [packedFlag,packedFlag]
def packedOverlapRegistry (_ : Roadmap.Address) := packedOverlap

theorem packed_overlap_detected : packedSeparationCheck packedOverlap = false ∧
    prepareSeparatedPackedSlot packedOverlapRegistry packedRegistry packedRequestA = none := ⟨rfl,rfl⟩

theorem packed_missing_byte_is_not_owned : packedOwnsByte packedPaths 7 ⟨26,by decide⟩ = false ∧
    packedOwnsByte packedPaths 7 ⟨25,by decide⟩ = true ∧
    packedOwnsByte packedPaths 8 ⟨31,by decide⟩ = true := by decide

/-- Deliberately wrong slot registration changes ownership; it is NOT a proof
of agreement with HashedLayout/solc. No checker can infer that missing owner law. -/
def packedWrongSlot : ScalarPath layout packedLayout := {packedFlag with slot := 8}
theorem packed_wrong_layout_discriminates : packedOwnsByte [packedWrongSlot] 7 ⟨0,by decide⟩ = false ∧
    packedOwnsByte [packedFlag] 7 ⟨0,by decide⟩ = true := by decide

theorem packed_erased_padding_wrong : complementWord (fun _ => true) packedRawA ≠ packedPlanA.residualUpdate.2 := by decide

def packedStepEnv : Source.Env := ⟨[]⟩
def packedStepRegistry (a : Roadmap.Address) : List (ScalarPath packedStepEnv.layout (packedStepEnv.lay a)) := []
def packedStepFrame : Source.Fr := ⟨account,account,0,false,"PackedStep",true,0⟩
def packedStepRequest : PackedSlotRequest := ⟨false,account,7,packedRawA⟩
theorem packed_step_plan_exists : (preparePackedSlot packedStepRegistry packedStepRegistry packedStepRequest).isSome := by decide
def packedStepPlan := (preparePackedSlot packedStepRegistry packedStepRegistry packedStepRequest).get packed_step_plan_exists

def packedStepState : Source.EMState packedStepEnv [] :=
  ⟨.nil,⟨⟨⟨fun _ => Source.Account.empty (D := packedStepEnv.layout) (packedStepEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩⟩⟩
def packedStepResidual := initialPackedComplement packedStepRegistry packedStepRegistry (fun _ => packedZeroRaw)

theorem packed_actual_static_refusal : packedSourceStep {packedStepFrame with static := true} packedStepPlan packedStepState packedStepResidual =
    ((.error (.revert []),packedStepState),packedStepResidual) := packedSourceStep_static _ _ _ _ rfl

theorem packed_actual_source_success : packedSourceStep packedStepFrame packedStepPlan packedStepState packedStepResidual =
    ((.ok (),(packedStepState.1,{packedStepState.2 with ex := packedStepState.2.ex.apply packedStepPlan.sourceOp})),residualWrite packedStepResidual packedStepPlan.residualUpdate) := packedSourceStep_nonstatic _ _ _ _ rfl

/-- Even a physically unchanged SSTORE remains refused by ACTUAL static rules. -/
theorem packed_actual_static_unchanged : packedSourceStep {packedStepFrame with static := true} packedStepPlan packedStepState
    (residualWrite packedStepResidual packedStepPlan.residualUpdate) =
    ((.error (.revert []),packedStepState),residualWrite packedStepResidual packedStepPlan.residualUpdate) := packedSourceStep_static _ _ _ _ rfl

end Solidity.Yul.Views.Controls
