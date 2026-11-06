import Solidity.Yul.Views.PackedResidualBoundaryControls
import Solidity.Yul.Views.PackedResidualFrame

namespace Solidity.Yul.Views.Controls

def packedTypedEnv : Source.Env := ⟨[
  ⟨.stateVar,"flag",some "Finite",false,.stateVar (.elem .bool) none none none false "flag" .none⟩,
  ⟨.stateVar,"small",some "Finite",false,.stateVar (.elem (.int false 16 (by decide))) none none none false "small" .none⟩,
  ⟨.stateVar,"data",some "Packed",false,.stateVar (.elem (.fixedBytes 3 (by decide))) none none none false "data" .none⟩,
  ⟨.stateVar,"who",some "Packed",false,.stateVar (.elem .address) none none none false "who" .none⟩]⟩

def packedTypedFlag : ScalarPath packedTypedEnv.layout (packedTypedEnv.lay account) := ⟨finiteFlag,7,boolField,boolCodec _,.bool⟩
def packedTypedSmall : ScalarPath packedTypedEnv.layout (packedTypedEnv.lay account) := ⟨finiteSmall,7,intField unsigned16 1 (by decide),intCodec _ unsigned16 1 (by decide),.int unsigned16⟩
def packedTypedBytes : ScalarPath packedTypedEnv.layout (packedTypedEnv.lay account) := ⟨packedBytesPath,7,fixedBytesField 3 (by decide) 3 (by decide),fixedBytesCodec _ 3 (by decide) 3 (by decide),.fixedBytes 3 (by decide)⟩
def packedTypedAddress : ScalarPath packedTypedEnv.layout (packedTypedEnv.lay account) := ⟨packedAddressPath,7,addressField 6 (by decide),addressCodec _ false 6 (by decide),.address false⟩
def packedTypedRegistry (a : Roadmap.Address) : List (ScalarPath packedTypedEnv.layout (packedTypedEnv.lay a)) := [packedTypedFlag,packedTypedSmall,packedTypedBytes,packedTypedAddress]

def packedTypedState : Source.EMState packedTypedEnv [] :=
  ⟨.nil,⟨⟨⟨fun _ => Source.Account.empty (D := packedTypedEnv.layout) (packedTypedEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩, Source.FailureExecution.Cursor.empty⟩⟩
def packedTypedResidual := initialPackedComplement packedTypedRegistry packedTypedRegistry (fun _ => packedZeroRaw)

theorem packed_typed_frame_prepares : (preparePackedFrame (ps := packedTypedRegistry) (ts := packedTypedRegistry) packedStepFrame false 7 packedRawA).isSome := by decide

def packedTypedPlan := (preparePackedFrame (ps := packedTypedRegistry) (ts := packedTypedRegistry) packedStepFrame false 7 packedRawA).get packed_typed_frame_prepares

def packedTypedRun := packedSourceStep packedStepFrame packedTypedPlan packedTypedState packedTypedResidual

theorem packed_typed_frame_bound : packedTypedPlan.request.address = packedStepFrame.this :=
  preparePackedFrame_address _ _ _ _ _ (Option.some_get packed_typed_frame_prepares).symm

theorem packed_typed_actual_success : packedTypedRun.1.1 = .ok () ∧ packedTypedRun.1.2.2.ex.journal.length = 1 ∧ packedTypedRun.2.journal.length = 1 := ⟨rfl,rfl,rfl⟩

theorem packed_typed_source_fields :
    (packedTypedRun.1.2.2.ex.world.accounts account).storage.read finiteFlag = some (.bool true) ∧
    (packedTypedRun.1.2.2.ex.world.accounts account).storage.read finiteSmall = some (.int 0x1234 (by decide)) ∧
    (packedTypedRun.1.2.2.ex.world.accounts account).storage.read packedBytesPath = some (.fixedBytes [0xff,0,0xaa] rfl) ∧
    (packedTypedRun.1.2.2.ex.world.accounts account).storage.read packedAddressPath = some (.address ⟨0x1234567890123456789012345678901234567890,by decide⟩) := ⟨rfl,rfl,rfl,rfl⟩

theorem packed_typed_initial_MemOK : Source.MemOK packedTypedEnv packedTypedState.2.heap.ty packedTypedState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem packed_typed_every_H_MemOK (H : Source.HeapTy) (ok : Source.MemOK packedTypedEnv H packedTypedState) :
    Source.MemOK packedTypedEnv H packedTypedRun.1.2 := packedSourceStep_MemOK H _ _ _ _ ok

theorem packed_typed_inhabited_MemOK : Source.MemOK packedTypedEnv packedTypedState.2.heap.ty packedTypedRun.1.2 := packed_typed_every_H_MemOK _ packed_typed_initial_MemOK

theorem packed_typed_actual_static_refusal : packedSourceStep {packedStepFrame with static := true} packedTypedPlan packedTypedState packedTypedResidual =
    ((.error (.revert []),packedTypedState),packedTypedResidual) := packedSourceStep_static _ _ _ _ rfl

theorem packed_typed_source_full_reencode :
    reencodePersistentSlot packedTypedRegistry ⟨packedTypedRun.1.2.2.ex,packedTypedRun.2⟩ account 7 = some packedRawA := by
  exact packedPersistent_reencode ⟨packedTypedState.2.ex,packedTypedResidual⟩ packedTypedPlan rfl ((packedSeparationCheck_iff _).mp (by decide))

theorem packed_typed_current_frame_step : packedFrameWrite? (ps := packedTypedRegistry) (ts := packedTypedRegistry)
    packedStepFrame false 7 packedRawA packedTypedState packedTypedResidual = some packedTypedRun := by
  unfold packedFrameWrite?
  rw [← Option.some_get packed_typed_frame_prepares,Option.map_some]
  rfl

theorem packed_typed_current_frame_reencode :
    reencodePersistentSlot packedTypedRegistry ⟨packedTypedRun.1.2.2.ex,packedTypedRun.2⟩ packedStepFrame.this 7 = some packedRawA :=
  packedFrameWrite_persistent_reencode _ _ _ _ _ _ packed_typed_current_frame_step rfl ((packedSeparationCheck_iff _).mp (by decide))

theorem packed_typed_child_prepares : (preparePackedFrame (ps := packedTypedRegistry) (ts := packedTypedRegistry) packedStepFrame false 7 packedRawB).isSome := by decide
def packedTypedChildPlan := (preparePackedFrame (ps := packedTypedRegistry) (ts := packedTypedRegistry) packedStepFrame false 7 packedRawB).get packed_typed_child_prepares
def packedTypedChildRun := packedSourceStep packedStepFrame packedTypedChildPlan packedTypedRun.1.2 packedTypedRun.2

def packedTypedCore : ResidualCompanion packedTypedEnv.layout packedTypedEnv.lay packedTypedEnv.lay complementCarrierOwnership := ⟨packedTypedState.2.ex,packedTypedResidual⟩
def packedTypedCallerCore : ResidualCompanion packedTypedEnv.layout packedTypedEnv.lay packedTypedEnv.lay complementCarrierOwnership := ⟨packedTypedRun.1.2.2.ex,packedTypedRun.2⟩
def packedTypedChildCore : ResidualCompanion packedTypedEnv.layout packedTypedEnv.lay packedTypedEnv.lay complementCarrierOwnership := ⟨packedTypedChildRun.1.2.2.ex,packedTypedChildRun.2⟩

theorem packed_typed_source_sequence_exact : packedTypedCallerCore = runPackedSlots packedTypedCore [packedTypedPlan] ∧
    packedTypedChildCore = runPackedSlots packedTypedCallerCore [packedTypedChildPlan] := ⟨rfl,rfl⟩

theorem packed_typed_actual_source_child_rollback : companionRollback (companionEnter packedTypedCallerCore account account 0 [] false)
    packedTypedChildCore = packedTypedCallerCore := packed_frame_rollback packedTypedCallerCore [packedTypedChildPlan] account account 0 [] false

theorem packed_typed_actual_source_outer_rollback : companionRollback (companionEnter packedTypedCore account account 0 [] false)
    (companionCommit (companionEnter packedTypedCallerCore account account 0 [] false) packedTypedChildCore) = packedTypedCore :=
  packed_frame_outer_commit packedTypedCore [packedTypedPlan] [packedTypedChildPlan] account account 0 [] false

theorem packed_typed_static_child_keeps_caller_prefix : packedSourceStep {packedStepFrame with static := true} packedTypedChildPlan packedTypedRun.1.2 packedTypedRun.2 =
    ((.error (.revert []),packedTypedRun.1.2),packedTypedRun.2) := packedSourceStep_static _ _ _ _ rfl

end Solidity.Yul.Views.Controls
