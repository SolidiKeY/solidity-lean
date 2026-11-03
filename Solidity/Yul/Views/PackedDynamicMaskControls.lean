import Solidity.Yul.Views.PackedDynamicSequence
import Solidity.Yul.Views.PackedDynamicValues

namespace Solidity.Yul.Views.Controls

def pdMaskShrink := packedMask (pdLayout.unsignedSnapshot pdFixed pdRaw1) pdRaw1
def pdMaskZero := packedMask (pdLayout.unsignedSnapshot pdFixed pdRaw0) pdRaw0
def pdMaskRegrow := packedMask (pdLayout.unsignedSnapshot pdFixed pdRaw18) pdRaw18

theorem pd_shrink_mask (q : Roadmap.Word) : pdShrink.step.2.cells (complementKey false account q) = pdMaskShrink q := by
  have mask := congrFun (pdShrink.complement rfl) q
  change _ = packedMask (pdLayout.unsignedSnapshot pdFixed pdShrink.nextRaw) pdShrink.nextRaw q at mask
  rw [pd_shrink_next] at mask
  exact mask

theorem pd_zero_mask (q : Roadmap.Word) : pdZero.step.2.cells (complementKey false account q) = pdMaskZero q := by
  have mask := congrFun (pdZero.complement rfl) q
  change _ = packedMask (pdLayout.unsignedSnapshot pdFixed pdZero.nextRaw) pdZero.nextRaw q at mask
  rw [pd_zero_next] at mask
  exact mask

theorem pd_shrink_newly_residual :
    pdShrink.step.2.cells (complementKey false account 1000) = ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000,by decide⟩ ∧
    pdShrink.step.2.cells (complementKey false account 1001) = pdWord1 := ⟨pd_shrink_mask 1000,pd_shrink_mask 1001⟩

theorem pd_zero_all_data_residual : pdZero.step.2.cells (complementKey false account 1000) = pdWord0 ∧
    pdZero.step.2.cells (complementKey false account 1001) = pdWord1 := ⟨pd_zero_mask 1000,pd_zero_mask 1001⟩

theorem pd_regrow_partial_padding : pdMaskRegrow 1001 = ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccc00000000,by decide⟩ := rfl

def pdArray : Source.STy := .array .storage (.int pdU16) none
def pdAliases : Source.EMState pdEnv [pdArray,pdArray] :=
  ⟨.cons pdX.reference (.cons pdX.reference .nil),pdRegrow.step.1.2.2⟩

theorem pd_alias_readLen : (Source.readLen (E := pdEnv) packedStepFrame (pdPath "xs")).run pdAliases = (.ok 18,pdAliases) := by
  have member := pdLayout.unsigned_root_member pdFixed pdRegrow.nextRaw (pdX.registration account) (pdLayout.unsignedHeader_member pdXEntry)
  have view := pdRegrow.view rfl (pdX.registration account) member
  have cell := pdX.view_length_cell account _ pdRegrow.nextRaw view
  have read := pdX.readLen packedStepFrame pdAliases (pdRegrow.nextRaw 0) rfl cell
  rw [pd_regrow_next] at read
  exact read

theorem pd_two_alias_lengths :
    (Source.lengthOf (E := pdEnv) packedStepFrame (pdAliases.1.get .here)).run pdAliases = (.ok 18,pdAliases) ∧
    (Source.lengthOf (E := pdEnv) packedStepFrame (pdAliases.1.get (.there .here))).run pdAliases = (.ok 18,pdAliases) :=
  ⟨pd_alias_readLen,pd_alias_readLen⟩

theorem pd_alias_tail_index : (Source.indexLoc (E := pdEnv) packedStepFrame (pdAliases.1.get (.there .here)) 16).run pdAliases =
    (.ok (.stor ⟨pdName "xs",[.index 16]⟩),pdAliases) := pdX.indexLoc packedStepFrame pdAliases 18 pd_alias_readLen 16

theorem pd_alias_tail_payload :
    (Source.readLoc (E := pdEnv) packedStepFrame (Source.Loc.stor (τ := .int pdU16) ⟨pdName "xs",[.index 16]⟩)).run pdAliases =
    (.ok (.int 77 (by decide)),pdAliases) := by
  have member : pdX.element pdFixed account 16 ∈ pdRegrow.next := by
    change _ ∈ pdLayout.unsignedSnapshot pdFixed pdRegrow.nextRaw
    rw [pd_regrow_next]
    exact pdLayout.unsigned_element_member pdFixed pdRaw18 pdXEntry 16 (by decide)
  have view := pdRegrow.view rfl (pdX.element pdFixed account 16) member
  have bank := pdLayout.unsigned_bank_agreement pdFixed pdRegrow.nextRaw _ member
  have read := pdX.read_element packedStepFrame pdAliases pdFixed 16 pdRegrow.nextRaw bank view
  rw [pd_regrow_next] at read
  exact read

theorem pd_alias_index_read :
    (do
      let loc ← Source.indexLoc (E := pdEnv) packedStepFrame (pdAliases.1.get (.there .here)) 16
      Source.readLoc packedStepFrame loc).run pdAliases = (.ok (.int 77 (by decide)),pdAliases) := by
  rw [Source.Hoare.run_bind,pd_alias_tail_index]
  exact pd_alias_tail_payload

theorem pd_alias_out_of_bounds : (Source.indexLoc (E := pdEnv) packedStepFrame (pdAliases.1.get .here) 18).run pdAliases =
    (.error (.revert (Source.panicData .index)),pdAliases) := pdX.indexLoc packedStepFrame pdAliases 18 pd_alias_readLen 18

theorem pd_newly_live17_payload :
    (Source.readLoc (E := pdEnv) packedStepFrame (Source.Loc.stor (τ := .int pdU16) ⟨pdName "xs",[.index 17]⟩)).run pdAliases =
      (.ok (.int 52428 (by decide)),pdAliases) := by
  have member : pdX.element pdFixed account 17 ∈ pdRegrow.next := by
    change _ ∈ pdLayout.unsignedSnapshot pdFixed pdRegrow.nextRaw
    rw [pd_regrow_next]
    exact pdLayout.unsigned_element_member pdFixed pdRaw18 pdXEntry 17 (by decide)
  have view := pdRegrow.view rfl (pdX.element pdFixed account 17) member
  have bank := pdLayout.unsigned_bank_agreement pdFixed pdRegrow.nextRaw _ member
  have read := pdX.read_element packedStepFrame pdAliases pdFixed 17 pdRegrow.nextRaw bank view
  rw [pd_regrow_next] at read
  exact read

end Solidity.Yul.Views.Controls
