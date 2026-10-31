import Solidity.Yul.Views.ScalarWorld
import Solidity.Yul.Views.PackedControls
import Solidity.Yul.Views.SourceControls

/-! Actual typed stores and journaled account/transient operations. Invalid
requests below are unsupported canonical preparation, not assembly semantics. -/
namespace Solidity.Yul.Views.Controls

def firstPath : Source.SPath := ⟨⟨some "Writeback", "first"⟩, []⟩
def secondPath : Source.SPath := ⟨⟨some "Writeback", "second"⟩, []⟩
def txPath : Source.SPath := ⟨⟨some "Writeback", "txFlag"⟩, []⟩
def scalarSlot : Roadmap.Word := ⟨7, by decide⟩
def secondField : Field := ⟨1, 1, by decide, by decide⟩
def firstCodec : ScalarCodec layout (allBool firstPath) boolField := boolCodec layout
def secondCodec : ScalarCodec layout (allBool secondPath) secondField := boolCodecAt layout 1 (by decide)
def emptyScalarStore : Source.Storage layout allBool := .empty
def explicitDefaultStore := emptyScalarStore.write firstPath (.bool false)
def scalarPhysicalStart : SlotView := patchScalarSlot
  (patchScalarSlot nonzeroSlots scalarSlot boolField (firstCodec.encode (.bool false)))
  scalarSlot secondField (secondCodec.encode (.bool false))
def firstPhysical : SlotView := patchScalarSlot scalarPhysicalStart scalarSlot boolField (firstCodec.encode (.bool true))
def bothPhysical : SlotView := patchScalarSlot firstPhysical scalarSlot secondField (secondCodec.encode (.bool true))
def invalidPhysical : SlotView := patchScalarSlot scalarPhysicalStart scalarSlot boolField ⟨2, by decide⟩

def concreteScalarObligations : ScalarStorageObligations layout allBool Unit :=
  singletonScalarObligations firstPath firstCodec .bool (fun _ => 0) (.root 7) (.bool false) rfl

theorem concrete_view_inhabited : concreteScalarObligations.view emptyScalarStore scalarPhysicalStart := rfl

theorem empty_and_explicit_default_preserved :
    canonicalPathWriteback firstPath firstCodec scalarSlot scalarPhysicalStart emptyScalarStore = some emptyScalarStore ∧
    canonicalPathWriteback firstPath firstCodec scalarSlot scalarPhysicalStart explicitDefaultStore = some explicitDefaultStore ∧
    emptyScalarStore.cell firstPath = none ∧ explicitDefaultStore.cell firstPath = some (.bool false) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem same_physical_default : encodeScalarPath firstPath firstCodec scalarSlot emptyScalarStore nonzeroSlots =
    encodeScalarPath firstPath firstCodec scalarSlot explicitDefaultStore nonzeroSlots := rfl

def changedScalarStore := preserveScalarWrite firstPath firstCodec (.bool true) emptyScalarStore

theorem actual_changed_writeback : canonicalPathWriteback firstPath firstCodec scalarSlot firstPhysical emptyScalarStore =
    some changedScalarStore ∧ changedScalarStore.cell firstPath = some (.bool true) ∧
    changedScalarStore.cell secondPath = none := by exact ⟨rfl, rfl, rfl⟩

theorem unchanged_physical_reconstruction : encodeScalarPath firstPath firstCodec scalarSlot changedScalarStore firstPhysical =
    some firstPhysical := encodeScalarPath_unchanged firstPath firstCodec scalarSlot _ _ rfl

theorem invalid_scalar_decode : canonicalPathWriteback firstPath firstCodec scalarSlot invalidPhysical changedScalarStore = none := rfl

def disjointScalarStore := preserveScalarWrite secondPath secondCodec (.bool true) changedScalarStore

theorem disjoint_actual_updates : canonicalPathWriteback secondPath secondCodec scalarSlot bothPhysical changedScalarStore =
    some disjointScalarStore ∧ disjointScalarStore.cell firstPath = some (.bool true) ∧
    disjointScalarStore.cell secondPath = some (.bool true) := by exact ⟨rfl, rfl, rfl⟩

theorem repeated_update_identity : preserveScalarWrite secondPath secondCodec (.bool true) disjointScalarStore = disjointScalarStore :=
  preserveScalarWrite_idempotent secondPath secondCodec (.bool true) changedScalarStore

theorem distinct_typed_updates_commute :
    preserveScalarWrite secondPath secondCodec (.bool true) changedScalarStore =
      preserveScalarWrite firstPath firstCodec (.bool true)
        (preserveScalarWrite secondPath secondCodec (.bool true) emptyScalarStore) :=
  preserveScalarWrite_commute secondPath firstPath secondCodec firstCodec _ _ _ (by decide)

theorem disjoint_field_value_preserved : boolField.findWord (bothPhysical scalarSlot) = firstCodec.encode (.bool true) := by
  rw [show bothPhysical = patchScalarSlot firstPhysical scalarSlot secondField (secondCodec.encode (.bool true)) from rfl,
    patchScalarSlot_other_field firstPhysical scalarSlot scalarSlot secondField boolField _ (Or.inr (Or.inr (by decide)))]
  exact patchScalarSlot_find scalarPhysicalStart scalarSlot boolField _

theorem writeback_padding_and_words : (scalarPhysicalStart scalarSlot).val =
      0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a50000 ∧
    (firstPhysical scalarSlot).val = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a50001 ∧
    (bothPhysical scalarSlot).val = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a50101 := by decide

theorem first_patch_residual_byte : slotBytes firstPhysical (7 * 32 + 2) = slotBytes scalarPhysicalStart (7 * 32 + 2) :=
  patchScalarSlot_unowned_byte scalarPhysicalStart scalarSlot boolField _ _ (by decide) (Or.inr (Or.inr (by decide)))

def firstSourceOp : Source.Op layout perAccount perAccount :=
  .account account (fun ac => {ac with storage := preserveScalarWrite firstPath firstCodec (.bool true) ac.storage})
def secondSourceOp : Source.Op layout perAccount perAccount :=
  .account account (fun ac => {ac with storage := preserveScalarWrite secondPath secondCodec (.bool true) ac.storage})
def transientPhysical : SlotView := patchScalarSlot (fun _ => 0) 0 boolField (firstCodec.encode (.bool true))
def txCodec : ScalarCodec layout (allBool txPath) boolField := boolCodec layout
def transientSourceOp : Source.Op layout perAccount perAccount := .transient account (preserveScalarWrite txPath txCodec (.bool true))

theorem concrete_account_requests : canonicalAccountWrite? account firstPath firstCodec scalarSlot firstPhysical = some firstSourceOp ∧
    canonicalAccountWrite? account secondPath secondCodec scalarSlot bothPhysical = some secondSourceOp := by
  constructor <;> rfl

theorem concrete_transient_request : canonicalTransientWrite? account txPath txCodec 0 transientPhysical = some transientSourceOp := rfl

theorem invalid_request_does_not_mutate_source :
    applyPreparedWrite initial (canonicalAccountWrite? account firstPath firstCodec scalarSlot invalidPhysical) = initial := rfl

def callerPrefix : Source.ExecState layout perAccount perAccount := initial.run [firstSourceOp]
def childChanges : List (Source.Op layout perAccount perAccount) := [secondSourceOp, transientSourceOp]
def successfulChild := callerPrefix.run childChanges

theorem current_state_not_stale : (successfulChild.world.accounts account).storage.cell firstPath = some (.bool true) ∧
    (successfulChild.world.accounts account).storage.cell secondPath = some (.bool true) ∧
    (successfulChild.transient.cells account).cell txPath = some (.bool true) ∧ successfulChild.journal.length = 3 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem inner_revert_with_caller_prefix :
    (callerPrefix.enter account account 0 [] false).rollback successfulChild = callerPrefix ∧
    (((callerPrefix.enter account account 0 [] false).rollback successfulChild).world.accounts account).storage.cell firstPath = some (.bool true) := by
  have h := Source.rollback_run callerPrefix childChanges account account 0 [] false
  change (callerPrefix.enter account account 0 [] false).rollback successfulChild = callerPrefix at h
  exact ⟨h, by rw [h]; rfl⟩

theorem child_success_then_outer_revert :
    (initial.enter account account 0 [] false).rollback
      ((callerPrefix.enter account account 0 [] false).commit successfulChild) = initial := by
  simpa only [Source.ExecState.run] using
    Source.rollback_outer_after_commit initial [firstSourceOp] childChanges [] account account 0 [] false

theorem successful_commit_and_transaction_reset :
    (callerPrefix.enter account account 0 [] false).commit successfulChild = successfulChild ∧
    (successfulChild.endTx.world.accounts account).storage.cell firstPath = some (.bool true) ∧
    (successfulChild.endTx.world.accounts account).storage.cell secondPath = some (.bool true) ∧
    (successfulChild.endTx.transient.cells account).cell txPath = none ∧ successfulChild.endTx.journal = [] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms concreteScalarObligations
#print axioms actual_changed_writeback
#print axioms inner_revert_with_caller_prefix
#print axioms child_success_then_outer_revert

end Solidity.Yul.Views.Controls
