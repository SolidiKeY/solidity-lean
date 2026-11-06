import Solidity.Yul.Views.ActualScalarReset
import Solidity.Yul.Views.ActualScalarTransientControls

/-! Full paired transient reset clears owned payload and unowned complement,
including unknown slots, after actual typed writes. Field-only reconstruction
retains padding and is deliberately distinguished from this physical reset. -/
namespace Solidity.Yul.Views.Controls

def arReached : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership :=
  ⟨atRepeat.1.2.2.ex,TransientSlotControls.residual⟩
def arReset := companionEndTx arReached

theorem ar_view_before : finiteView (rootTempRegistry account) (atBefore.2.ex.transient.cells account) atRaw := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro c member
  change c∈[atCell] at member
  have same := List.mem_singleton.mp member
  subst c
  rfl

theorem ar_registry_reencode : finiteEncode (rootTempRegistry account)
    (atWrite.1.2.2.ex.transient.cells account)
    (fun q=>TransientSlotControls.residual.cells (complementKey true account q))=some atWrite.2 :=
  actualScalarWrite_transient_registry_reencode TransientSlotControls.frame atBefore (rootTempRegistry account) atCell
    List.mem_cons_self ((packedSeparationCheck_iff _).mp (by decide)) atRaw ar_view_before _ rfl rfl TransientSlotControls.residual rfl

theorem ar_before_payload : transientSlotLoad rootTempRegistry arReached account 0=some 0xbeefabcd := rfl

theorem ar_before_unknown : transientSlotLoad rootTempRegistry arReached account 99=some 0xbeef0000 := rfl

theorem ar_every_account_slot (a : Roadmap.Address) (slot : Roadmap.Word) :
    transientSlotLoad rootTempRegistry arReset a slot=some 0 :=
  actualScalarWrite_endTx_load TransientSlotControls.frame atWrite.1.2 atCell (Source.intWrap unsigned16 0xabcd)
    atWrite.2 TransientSlotControls.residual rootTempRegistry TransientSlotControls.actual_zero_defaults a slot

theorem ar_persistent_survives : (arReset.source.world.accounts account).storage.read (rootPath "a")=
    some (Source.intWrap rootU8 7) := rfl

theorem ar_journals_closed : arReset.source.journal=[] ∧ arReset.residual.journal=[] := ⟨rfl,rfl⟩

theorem ar_padding_cleared : arReset.residual.cells (complementKey true account 0)=0 := rfl

theorem ar_field_only_is_wrong_reset :
    some (patchScalarSlot atRepeat.2 atCell.slot atCell.field (atCell.codec.encode (Source.intWrap unsigned16 0)) 0)≠
      transientSlotLoad rootTempRegistry arReset account 0 := by
  decide
end Solidity.Yul.Views.Controls
