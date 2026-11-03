import Solidity.Yul.Views.PackedResidualWritebackSound
import Solidity.Yul.Views.FiniteResidualControls

namespace Solidity.Yul.Views.Controls

def packedBytesPath : Source.SPath := ⟨⟨some "Packed", "data"⟩,[]⟩
def packedAddressPath : Source.SPath := ⟨⟨some "Packed", "who"⟩,[]⟩
def packedLayout (p : Source.SPath) : Source.STy :=
  if p = finiteFlag then .bool else if p = finiteSmall then .int unsigned16 else
  if p = packedBytesPath then .fixedBytes 3 (by decide) else if p = packedAddressPath then .address false else .int .u256

def packedFlag : ScalarPath layout packedLayout := ⟨finiteFlag,7,boolField,boolCodec layout,.bool⟩
def packedSmall : ScalarPath layout packedLayout := ⟨finiteSmall,7,intField unsigned16 1 (by decide),intCodec layout unsigned16 1 (by decide),.int unsigned16⟩
def packedBytes : ScalarPath layout packedLayout := ⟨packedBytesPath,7,fixedBytesField 3 (by decide) 3 (by decide),fixedBytesCodec layout 3 (by decide) 3 (by decide),.fixedBytes 3 (by decide)⟩
def packedAddress : ScalarPath layout packedLayout := ⟨packedAddressPath,7,addressField 6 (by decide),addressCodec layout false 6 (by decide),.address false⟩
def packedWide : ScalarPath layout packedLayout := ⟨finiteWide,8,intField .u256 0 (by decide),intCodec layout .u256 0 (by decide),.int .u256⟩
def packedPaths := [packedFlag,packedSmall,packedBytes,packedAddress,packedWide]
def packedPerAccount : Roadmap.Address → Source.SPath → Source.STy := fun _ => packedLayout
def packedRegistry (_ : Roadmap.Address) := packedPaths

theorem packed_paths_separated : finiteSeparated packedPaths := (packedSeparationCheck_iff _).mp (by decide)

def packedZeroRaw : Roadmap.Word := ⟨0xa5a5a5a5a5a5 * 256^26,by decide⟩
def packedRawA : Roadmap.Word := ⟨0xa5a5a5a5a5a5 * 256^26 + 0x1234567890123456789012345678901234567890 * 256^6 + 0xff00aa*256^3 + 0x1234*256 + 1,by decide⟩
def packedRawB : Roadmap.Word := ⟨0x5a5a5a5a5a5a * 256^26 + 0xabcdefabcdefabcdefabcdefabcdefabcdefabcd * 256^6 + 0x112233*256^3 + 0xbeef*256,by decide⟩
def packedRequestA : PackedSlotRequest := ⟨false,account,7,packedRawA⟩
def packedRequestB : PackedSlotRequest := ⟨false,account,7,packedRawB⟩
def packedRequestT : PackedSlotRequest := ⟨true,account,7,packedRawB⟩

theorem packed_planA_exists : (preparePackedSlot packedRegistry packedRegistry packedRequestA).isSome := by decide
theorem packed_planB_exists : (preparePackedSlot packedRegistry packedRegistry packedRequestB).isSome := by decide
theorem packed_planT_exists : (preparePackedSlot packedRegistry packedRegistry packedRequestT).isSome := by decide

def packedPlanA := (preparePackedSlot packedRegistry packedRegistry packedRequestA).get packed_planA_exists
def packedPlanB := (preparePackedSlot packedRegistry packedRegistry packedRequestB).get packed_planB_exists
def packedPlanT := (preparePackedSlot packedRegistry packedRegistry packedRequestT).get packed_planT_exists

def packedInitialStore : Source.Storage layout packedLayout := Source.Storage.empty.write finiteUnrelated (.int 55 (by decide))
def packedInitialSource : Source.ExecState layout packedPerAccount packedPerAccount :=
  ⟨⟨fun _ => {Source.Account.empty (D := layout) packedLayout with storage := packedInitialStore}⟩,.empty,[]⟩
def packedInitial : ResidualCompanion layout packedPerAccount packedPerAccount complementCarrierOwnership :=
  ⟨packedInitialSource,initialPackedComplement packedRegistry packedRegistry (fun _ => packedZeroRaw)⟩
def packedCaller := runPackedSlots packedInitial [packedPlanA]
def packedChild := runPackedSlots packedCaller [packedPlanB,packedPlanT]
def packedPersistentKey := complementKey false account 7
def packedTransientKey := complementKey true account 7

theorem packed_initial_valid : PackedComplementValid packedRegistry packedRegistry packedInitial.residual := initialPackedComplement_valid _
theorem packed_child_valid : PackedComplementValid packedRegistry packedRegistry packedChild.residual :=
  packedComplement_run _ (packedComplement_run _ packed_initial_valid [packedPlanA]) [packedPlanB,packedPlanT]

theorem packed_actual_fields :
    (packedCaller.source.world.accounts account).storage.cell finiteFlag = some (.bool true) ∧
    (packedCaller.source.world.accounts account).storage.cell finiteSmall = some (.int 0x1234 (by decide)) ∧
    (packedCaller.source.world.accounts account).storage.cell packedBytesPath = some (.fixedBytes [0xff,0,0xaa] rfl) ∧
    (packedCaller.source.world.accounts account).storage.cell packedAddressPath = some (.address ⟨0x1234567890123456789012345678901234567890,by decide⟩) := ⟨rfl,rfl,rfl,rfl⟩

theorem packed_full_raw_persistent : reencodePersistentSlot packedRegistry packedCaller account 7 = some packedRawA := packedPersistent_reencode _ packedPlanA rfl packed_paths_separated

theorem packed_full_raw_child : reencodePersistentSlot packedRegistry packedChild account 7 = some packedRawB ∧
    reencodeTransientSlot packedRegistry packedChild account 7 = some packedRawB := by
  constructor
  · exact packedPersistent_reencode _ packedPlanB rfl packed_paths_separated
  · exact packedTransient_reencode _ packedPlanT rfl packed_paths_separated

theorem packed_nonzero_padding_exact :
    lowByte (packedCaller.residual.cells packedPersistentKey) ⟨26,by decide⟩ = 0xa5 ∧
    lowByte (packedChild.residual.cells packedPersistentKey) ⟨31,by decide⟩ = 0x5a ∧
    lowByte (packedChild.residual.cells packedTransientKey) ⟨31,by decide⟩ = 0x5a ∧
    lowByte (packedChild.residual.cells packedPersistentKey) ⟨3,by decide⟩ = 0 := by decide

theorem packed_other_path_account_bank :
    (packedChild.source.world.accounts account).storage.cell finiteUnrelated = some (.int 55 (by decide)) ∧
    (packedChild.source.world.accounts account).storage.cell finiteWide = none ∧
    (packedChild.source.world.accounts (⟨2,by decide⟩)).storage.cell finiteFlag = none ∧
    lowByte (packedChild.residual.cells (complementKey false ⟨2,by decide⟩ 7)) ⟨31,by decide⟩ = 0xa5 := ⟨rfl,rfl,rfl,by decide⟩

theorem packed_nested_child_rollback : companionRollback (companionEnter packedCaller account account 0 [] false) packedChild = packedCaller :=
  packed_frame_child_rollback packedInitial [packedPlanA] [packedPlanB,packedPlanT] account account 0 [] false

theorem packed_child_success_enclosing_rollback : companionRollback (companionEnter packedInitial account account 0 [] false)
    (companionCommit (companionEnter packedCaller account account 0 [] false) packedChild) = packedInitial :=
  packed_frame_outer_commit packedInitial [packedPlanA] [packedPlanB,packedPlanT] account account 0 [] false

theorem packed_repeated_same_slot_order :
    reencodePersistentSlot packedRegistry (runPackedSlots packedInitial [packedPlanA,packedPlanB]) account 7 = some packedRawB ∧
    reencodePersistentSlot packedRegistry (runPackedSlots packedInitial [packedPlanB,packedPlanA]) account 7 = some packedRawA ∧ packedRawA ≠ packedRawB :=
  ⟨packedPersistent_reencode _ packedPlanB rfl packed_paths_separated,packedPersistent_reencode _ packedPlanA rfl packed_paths_separated,by decide⟩

theorem packed_journal_pair : packedChild.source.journal.length = 3 ∧ packedChild.residual.journal.length = 3 := ⟨rfl,rfl⟩

end Solidity.Yul.Views.Controls
