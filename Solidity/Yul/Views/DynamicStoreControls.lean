import Solidity.Yul.Views.DynamicControls
import Solidity.Yul.Views.DynamicLengthWorld

namespace Solidity.Yul.Views.Controls

/-- Finite canonical snapshot control. Hash values here inhabit the explicit
run's separation algebra; they are NOT the numeric real-keccak outputs. -/
def dynRegistry (a : Roadmap.Address) : List (ScalarPath dynEnv.layout (dynEnv.lay a)) :=
  dynComputed.registrations ++ [dynX.element dynTestFixed a 0,dynX.element dynTestFixed a 1,dynY.element dynTestFixed a 0]

def dynRaw42 : Roadmap.Word := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff11,by decide⟩
def dynRaw44 : Roadmap.Word := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc1234,by decide⟩
def dynMax : Roadmap.Word := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,by decide⟩
def dynSnapshot : SlotView := fun q =>
  if q = 42 then dynRaw42 else if q = 43 then 2 else if q = 44 then dynRaw44 else if q = 45 then 1
  else if q = 46 then 55 else if q = 1000 then 12 else if q = 1001 then dynMax else if q = 2000 then 33 else 77

def dynStorageState : Source.EMState dynEnv [] :=
  ⟨.nil,⟨⟨⟨fun _ => Source.Account.empty (D := dynEnv.layout) (dynEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩⟩⟩

theorem dyn_registry_separated : finiteSeparated (dynRegistry account) :=
  (packedSeparationCheck_iff _).mp (by decide)

theorem dyn_store_ready : (packedStoreWriteback (dynRegistry account) dynSnapshot
    (dynStorageState.2.ex.world.accounts account).storage).isSome := by decide

def dynStore := (packedStoreWriteback (dynRegistry account) dynSnapshot
  (dynStorageState.2.ex.world.accounts account).storage).get dyn_store_ready

theorem dyn_whole_raw_reconstruction : finiteEncode (dynRegistry account) dynStore.1 dynStore.2 = some dynSnapshot :=
  packedStoreWriteback_reencode _ _ _ _ _ dyn_registry_separated (Option.get_mem dyn_store_ready)

theorem dyn_written_lengths_and_data :
    dynStore.1.read (dynPath "xs") = some (.int 2 (by decide)) ∧
    dynStore.1.read (dynPath "ys") = some (.int 1 (by decide)) ∧
    dynStore.1.read ⟨dynName "xs",[.index 0]⟩ = some (.int 12 (by decide)) ∧
    dynStore.1.read ⟨dynName "xs",[.index 1]⟩ = some (.int (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (by decide)) ∧
    dynStore.1.read ⟨dynName "ys",[.index 0]⟩ = some (.int 33 (by decide)) := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem dyn_padding_and_unknown_tail : dynStore.2 44 =
    ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc0000,by decide⟩ ∧
    dynStore.2 1002 = 77 ∧ dynStore.2 47 = 77 := ⟨rfl,rfl,rfl⟩

def dynWrittenState : Source.EMState dynEnv [] :=
  (dynStorageState.1,{dynStorageState.2 with ex := {dynStorageState.2.ex with world := dynStorageState.2.ex.world.set account {dynStorageState.2.ex.world.accounts account with storage := dynStore.1}}})

theorem dyn_actual_lengths : (Source.readLen (E := dynEnv) packedStepFrame (dynPath "xs")).run dynWrittenState = (.ok 2,dynWrittenState) ∧
    (Source.readLen (E := dynEnv) packedStepFrame (dynPath "ys")).run dynWrittenState = (.ok 1,dynWrittenState) :=
  ⟨dynX.readLen _ _ 2 rfl rfl,dynY.readLen _ _ 1 rfl rfl⟩

theorem dyn_actual_bound_success : (Source.indexLoc (E := dynEnv) packedStepFrame dynX.reference 1).run dynWrittenState =
    (.ok (.stor ⟨dynName "xs",[.index 1]⟩),dynWrittenState) := dynX.indexLoc _ _ 2 dyn_actual_lengths.1 1

theorem dyn_actual_bound_error : (Source.indexLoc (E := dynEnv) packedStepFrame dynX.reference 2).run dynWrittenState =
    (.error (.revert (Source.panicData .index)),dynWrittenState) := dynX.indexLoc _ _ 2 dyn_actual_lengths.1 2

/-- Ordinary writeLen administration deliberately differs from pure view
preparation: even zero creates Some zero and a source journal entry. -/
def dynOrdinaryZero := (Source.writeLen (E := dynEnv) packedStepFrame (dynPath "xs") 0).run dynStorageState

theorem dyn_ordinary_zero_is_explicit : dynOrdinaryZero.1 = .ok () ∧
    (dynOrdinaryZero.2.2.ex.world.accounts account).storage.cell (dynPath "xs") = some (.int 0 (by decide)) ∧
    dynOrdinaryZero.2.2.ex.journal.length = 1 ∧
    (dynStorageState.2.ex.world.accounts account).storage.cell (dynPath "xs") = none := ⟨rfl,rfl,rfl,rfl⟩

theorem dyn_ordinary_static :
    (Source.writeLen (E := dynEnv) (Γ := []) {packedStepFrame with static := true} (dynPath "xs") 0).run dynStorageState =
    (.error (.revert []),dynStorageState) := dynX.writeLen_run _ _ _ rfl

theorem dyn_initial_MemOK : Source.MemOK dynEnv dynStorageState.2.heap.ty dynStorageState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem dyn_ordinary_every_H (H : Source.HeapTy) (ok : Source.MemOK dynEnv H dynStorageState) :
    Source.MemOK dynEnv H dynOrdinaryZero.2 := dynX.writeLen_MemOK _ _ _ H rfl ok

end Solidity.Yul.Views.Controls
