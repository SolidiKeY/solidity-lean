import Solidity.Yul.Views.SignedDynamicSequence
import Solidity.Yul.Views.IntDynamicValues

namespace Solidity.Yul.Views.Controls

def sdMaskShrink := packedMask (sdLayout.integerSnapshot sdFixed sdRaw1) sdRaw1
def sdMaskZero := packedMask (sdLayout.integerSnapshot sdFixed sdRaw0) sdRaw0
def sdMaskRegrow := packedMask (sdLayout.integerSnapshot sdFixed sdRaw18) sdRaw18

theorem sd_shrink_mask (q : Roadmap.Word) : sdShrink.step.2.cells (complementKey false account q) = sdMaskShrink q := by
  have mask := congrFun (sdShrink.complement rfl) q
  change _ = packedMask (sdLayout.integerSnapshot sdFixed sdShrink.nextRaw) sdShrink.nextRaw q at mask
  rw [sd_shrink_next] at mask
  exact mask

theorem sd_zero_mask (q : Roadmap.Word) : sdZero.step.2.cells (complementKey false account q) = sdMaskZero q := by
  have mask := congrFun (sdZero.complement rfl) q
  change _ = packedMask (sdLayout.integerSnapshot sdFixed sdZero.nextRaw) sdZero.nextRaw q at mask
  rw [sd_zero_next] at mask
  exact mask

theorem sd_shrink_newly_residual :
    sdShrink.step.2.cells (complementKey false account 1000) = ⟨0xffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000ffff7fff0000,by decide⟩ ∧
    sdShrink.step.2.cells (complementKey false account 1001) = sdWord1 := ⟨sd_shrink_mask 1000,sd_shrink_mask 1001⟩

theorem sd_zero_all_data_residual : sdZero.step.2.cells (complementKey false account 1000) = sdWord0 ∧
    sdZero.step.2.cells (complementKey false account 1001) = sdWord1 := ⟨sd_zero_mask 1000,sd_zero_mask 1001⟩

theorem sd_regrow_partial_padding : sdMaskRegrow 1001 = ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccc00000000,by decide⟩ := rfl

def sdArray : Source.STy := .array .storage (.int sdI16) none
def sdAliases : Source.EMState sdEnv [sdArray,sdArray] :=
  ⟨.cons sdX.reference (.cons sdX.reference .nil),sdRegrow.step.1.2.2⟩

theorem sd_alias_readLen : (Source.readLen (E := sdEnv) packedStepFrame (sdPath "xs")).run sdAliases = (.ok 18,sdAliases) := by
  have member := sdLayout.integer_root_member sdFixed sdRegrow.nextRaw (sdX.registration account) (sdLayout.integerHeader_member sdXEntry)
  have view := sdRegrow.view rfl (sdX.registration account) member
  have cell := sdX.view_length_cell account _ sdRegrow.nextRaw view
  have read := sdX.readLen packedStepFrame sdAliases (sdRegrow.nextRaw 0) rfl cell
  rw [sd_regrow_next] at read
  exact read

theorem sd_two_alias_lengths :
    (Source.lengthOf (E := sdEnv) packedStepFrame (sdAliases.1.get .here)).run sdAliases = (.ok 18,sdAliases) ∧
    (Source.lengthOf (E := sdEnv) packedStepFrame (sdAliases.1.get (.there .here))).run sdAliases = (.ok 18,sdAliases) :=
  ⟨sd_alias_readLen,sd_alias_readLen⟩

theorem sd_alias_tail_index : (Source.indexLoc (E := sdEnv) packedStepFrame (sdAliases.1.get (.there .here)) 16).run sdAliases =
    (.ok (.stor ⟨sdName "xs",[.index 16]⟩),sdAliases) := sdX.indexLoc packedStepFrame sdAliases 18 sd_alias_readLen 16

theorem sd_alias_tail_payload :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI16) ⟨sdName "xs",[.index 16]⟩)).run sdAliases =
    (.ok (.int (-1) (by decide)),sdAliases) := by
  have member : sdX.element sdFixed account 16 ∈ sdRegrow.next := by
    change _ ∈ sdLayout.integerSnapshot sdFixed sdRegrow.nextRaw
    rw [sd_regrow_next]
    exact sdLayout.integer_element_member sdFixed sdRaw18 sdXEntry 16 (by decide)
  have view := sdRegrow.view rfl (sdX.element sdFixed account 16) member
  have bank := sdLayout.integer_bank_agreement sdFixed sdRegrow.nextRaw _ member
  have read := sdX.read_element packedStepFrame sdAliases sdFixed 16 sdRegrow.nextRaw bank view
  rw [sd_regrow_next] at read
  exact read

theorem sd_alias_index_read :
    (do
      let loc ← Source.indexLoc (E := sdEnv) packedStepFrame (sdAliases.1.get (.there .here)) 16
      Source.readLoc packedStepFrame loc).run sdAliases = (.ok (.int (-1) (by decide)),sdAliases) := by
  rw [Source.Hoare.run_bind,sd_alias_tail_index]
  exact sd_alias_tail_payload

theorem sd_alias_out_of_bounds : (Source.indexLoc (E := sdEnv) packedStepFrame (sdAliases.1.get .here) 18).run sdAliases =
    (.error (.revert (Source.panicData .index)),sdAliases) := sdX.indexLoc packedStepFrame sdAliases 18 sd_alias_readLen 18

theorem sd_newly_live17_payload :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI16) ⟨sdName "xs",[.index 17]⟩)).run sdAliases =
      (.ok (.int (-32768) (by decide)),sdAliases) := by
  have member : sdX.element sdFixed account 17 ∈ sdRegrow.next := by
    change _ ∈ sdLayout.integerSnapshot sdFixed sdRegrow.nextRaw
    rw [sd_regrow_next]
    exact sdLayout.integer_element_member sdFixed sdRaw18 sdXEntry 17 (by decide)
  have view := sdRegrow.view rfl (sdX.element sdFixed account 17) member
  have bank := sdLayout.integer_bank_agreement sdFixed sdRegrow.nextRaw _ member
  have read := sdX.read_element packedStepFrame sdAliases sdFixed 17 sdRegrow.nextRaw bank view
  rw [sd_regrow_next] at read
  exact read

end Solidity.Yul.Views.Controls
