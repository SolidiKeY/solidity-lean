import Solidity.Yul.Views.OwnedBoolPreparation
import Solidity.Yul.Views.PrimitiveDynamicBoundaryControls

namespace Solidity.Yul.Views.Controls

def dbGrowRaw := saveSlot pcRaw 3 4
def dbZeroRaw := saveSlot dbGrowRaw 3 0
def dbAgainRaw := saveSlot dbZeroRaw 3 4

theorem db_initial_nonbool : ∀ c ∈ pcLayout.primitiveSnapshot pcFixed pcRaw, pcEnv.lay account c.path≠.bool := by decide

theorem db_initial_encoding : finiteEncode
    (representedRegistry (pcLayout.primitiveSnapshot pcFixed pcRaw) false account boolEncodingInitial)
    (pcState.2.ex.world.accounts account).storage (fun q => pcResidual.cells (complementKey false account q))=some pcRaw := by
  rw [representedRegistry_nonbool _ _ _ _ db_initial_nonbool]
  exact pc_initial_encoding

theorem db_initial_check : packedSeparationCheck (pcLayout.primitiveSnapshot pcFixed pcRaw)=true := by
  rw [pc_empty_inventory]
  exact (packedSeparationCheck_iff _).mpr pcLayout.separated

theorem db_grow_check : packedSeparationCheck (pcLayout.primitiveSnapshot pcFixed dbGrowRaw)=true := by decide

theorem db_zero_check : packedSeparationCheck (pcLayout.primitiveSnapshot pcFixed dbZeroRaw)=true := by decide

theorem db_again_check : packedSeparationCheck (pcLayout.primitiveSnapshot pcFixed dbAgainRaw)=true := by decide

theorem db_nonbool_grow : ∀ c ∈ pcLayout.primitiveSnapshot pcFixed dbGrowRaw, pcEnv.lay account c.path≠.bool →
    (canonicalScalarDecode c.codec (c.field.findWord (dbGrowRaw c.slot))).isSome := by decide

theorem db_grow_decode : (finiteAccountWrite? (T:=pcEnv.lay) account
    (representedRegistry (pcLayout.primitiveSnapshot pcFixed dbGrowRaw) false account
      (primitiveEncodingNext pcLayout pcFixed dbGrowRaw boolEncodingInitial)) dbGrowRaw).isSome := by
  simpa only [finiteAccountWrite?,Option.isSome_map] using
    (representedPrepare_found (pcLayout.primitiveSnapshot pcFixed dbGrowRaw) false account boolEncodingInitial dbGrowRaw
      ((packedSeparationCheck_iff _).mp (by decide)) db_nonbool_grow)

def dbGrowOp : Source.Op pcEnv.layout pcEnv.lay pcEnv.lay :=
  (finiteAccountWrite? account (representedRegistry (pcLayout.primitiveSnapshot pcFixed dbGrowRaw) false account
    (primitiveEncodingNext pcLayout pcFixed dbGrowRaw boolEncodingInitial)) dbGrowRaw).get db_grow_decode

@[irreducible]
def dbGrow : RepresentedOwnershipPlan packedStepFrame pcLayout pcFixed 3 4 pcState pcResidual boolEncodingInitial :=
  ⟨pcLayout.primitiveSnapshot pcFixed pcRaw,
   pcLayout.primitiveSourceInventory_view packedStepFrame pcFixed pcState pcRaw pc_initial_view,
   pcRaw,db_initial_encoding,db_initial_check,db_grow_check,dbGrowOp,Option.get_mem db_grow_decode⟩

theorem db_grow_next : dbGrow.nextRaw=dbGrowRaw := by unfold dbGrow; rfl

theorem db_nonbool_zero : ∀ c ∈ pcLayout.primitiveSnapshot pcFixed dbZeroRaw, pcEnv.lay account c.path≠.bool →
    (canonicalScalarDecode c.codec (c.field.findWord (dbZeroRaw c.slot))).isSome := by decide

theorem db_zero_decode : (finiteAccountWrite? (T:=pcEnv.lay) account
    (representedRegistry (pcLayout.primitiveSnapshot pcFixed dbZeroRaw) false account
      (primitiveEncodingNext pcLayout pcFixed dbZeroRaw dbGrow.step.2)) dbZeroRaw).isSome := by
  simpa only [finiteAccountWrite?,Option.isSome_map] using
    (representedPrepare_found (pcLayout.primitiveSnapshot pcFixed dbZeroRaw) false account dbGrow.step.2 dbZeroRaw
      ((packedSeparationCheck_iff _).mp (by decide)) db_nonbool_zero)

def dbZeroOp : Source.Op pcEnv.layout pcEnv.lay pcEnv.lay :=
  (finiteAccountWrite? account (representedRegistry (pcLayout.primitiveSnapshot pcFixed dbZeroRaw) false account
    (primitiveEncodingNext pcLayout pcFixed dbZeroRaw dbGrow.step.2)) dbZeroRaw).get db_zero_decode

@[irreducible]
def dbZero : RepresentedOwnershipPlan packedStepFrame pcLayout pcFixed 3 0 dbGrow.step.1.1.2 dbGrow.step.1.2 dbGrow.step.2 :=
  ⟨pcLayout.primitiveSnapshot pcFixed dbGrowRaw,
   (by simpa only [db_grow_next] using dbGrow.refreshed rfl),
   dbGrowRaw,(by simpa only [db_grow_next] using dbGrow.reencode_current rfl),
   db_grow_check,db_zero_check,dbZeroOp,Option.get_mem db_zero_decode⟩

theorem db_zero_next : dbZero.nextRaw=dbZeroRaw := by unfold dbZero; rfl

theorem db_nonbool_again : ∀ c ∈ pcLayout.primitiveSnapshot pcFixed dbAgainRaw, pcEnv.lay account c.path≠.bool →
    (canonicalScalarDecode c.codec (c.field.findWord (dbAgainRaw c.slot))).isSome := by decide

theorem db_again_decode : (finiteAccountWrite? (T:=pcEnv.lay) account
    (representedRegistry (pcLayout.primitiveSnapshot pcFixed dbAgainRaw) false account
      (primitiveEncodingNext pcLayout pcFixed dbAgainRaw dbZero.step.2)) dbAgainRaw).isSome := by
  simpa only [finiteAccountWrite?,Option.isSome_map] using
    (representedPrepare_found (pcLayout.primitiveSnapshot pcFixed dbAgainRaw) false account dbZero.step.2 dbAgainRaw
      ((packedSeparationCheck_iff _).mp (by decide)) db_nonbool_again)

def dbAgainOp : Source.Op pcEnv.layout pcEnv.lay pcEnv.lay :=
  (finiteAccountWrite? account (representedRegistry (pcLayout.primitiveSnapshot pcFixed dbAgainRaw) false account
    (primitiveEncodingNext pcLayout pcFixed dbAgainRaw dbZero.step.2)) dbAgainRaw).get db_again_decode

@[irreducible]
def dbAgain : RepresentedOwnershipPlan packedStepFrame pcLayout pcFixed 3 4 dbZero.step.1.1.2 dbZero.step.1.2 dbZero.step.2 :=
  ⟨pcLayout.primitiveSnapshot pcFixed dbZeroRaw,
   (by simpa only [db_zero_next] using dbZero.refreshed rfl),
   dbZeroRaw,(by simpa only [db_zero_next] using dbZero.reencode_current rfl),
   db_zero_check,db_again_check,dbAgainOp,Option.get_mem db_again_decode⟩

theorem db_again_next : dbAgain.nextRaw=dbAgainRaw := by unfold dbAgain; rfl

theorem db_grow_fresh : prepareRepresentedOwnership? packedStepFrame pcLayout pcFixed 3 4 pcState pcResidual boolEncodingInitial=some dbGrow := dbGrow.prepare_eq

theorem db_grow_full_map : finiteEncode dbGrow.next (dbGrow.after.source.world.accounts account).storage
    (fun q => dbGrow.after.residual.cells (complementKey false account q))=some dbGrowRaw :=
  (dbGrow.reencode rfl).trans (congrArg some db_grow_next)

theorem db_regrow_full_map : finiteEncode dbAgain.next (dbAgain.after.source.world.accounts account).storage
    (fun q => dbAgain.after.residual.cells (complementKey false account q))=some dbAgainRaw :=
  (dbAgain.reencode rfl).trans (congrArg some db_again_next)

theorem db_every_H (H : Source.HeapTy) (ok : Source.MemOK pcEnv H pcState) :
    Source.MemOK pcEnv H dbAgain.step.1.1.2 := dbAgain.MemOK H (dbZero.MemOK H (dbGrow.MemOK H ok))

end Solidity.Yul.Views.Controls
