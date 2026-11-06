import Solidity.Yul.Views.ScalarFamilyNegativeControls

namespace Solidity.Yul.Views.Controls

def sfArray : Source.STy := .array .storage .bool none
def sfAliases : Source.EMState sfEnv [sfArray,sfArray] :=
  ⟨.cons sfX.reference (.cons sfX.reference .nil),sfZFill.step.1.2.2⟩

theorem sf_alias_readLen : (Source.readLen (E := sfEnv) packedStepFrame (sfPath "xs")).run sfAliases = (.ok 34,sfAliases) := by
  have member := sfLayout.scalarFamily_root_member sfFixed sfZFill.nextRaw (sfX.registration account) (sfLayout.scalarFamilyHeader_member sfXEntry)
  have view := sfZFill.view rfl (sfX.registration account) member
  have cell := sfX.view_length_cell account _ sfZFill.nextRaw view
  have read := sfX.readLen packedStepFrame sfAliases (sfZFill.nextRaw 0) rfl cell
  rw [sfzfill_next] at read
  exact read

theorem sf_two_alias_lengths :
    (Source.lengthOf (E := sfEnv) packedStepFrame (sfAliases.1.get .here)).run sfAliases = (.ok 34,sfAliases) ∧
    (Source.lengthOf (E := sfEnv) packedStepFrame (sfAliases.1.get (.there .here))).run sfAliases = (.ok 34,sfAliases) :=
  ⟨sf_alias_readLen,sf_alias_readLen⟩

theorem sf_alias_tail_index : (Source.indexLoc (E := sfEnv) packedStepFrame (sfAliases.1.get (.there .here)) 33).run sfAliases =
    (.ok (.stor ⟨sfName "xs",[.index 33]⟩),sfAliases) := sfX.indexLoc packedStepFrame sfAliases 34 sf_alias_readLen 33


theorem sf_alias_bool_read :
    (Source.readLoc (E := sfEnv) packedStepFrame (Source.Loc.stor (τ := .bool) ⟨sfName "xs",[.index 33]⟩)).run sfAliases =
    (.ok (.bool true),sfAliases) := by
  have member : sfX.element sfFixed account 33 ∈ sfZFill.next := by
    change _ ∈ sfLayout.scalarFamilySnapshot sfFixed sfZFill.nextRaw
    rw [sfzfill_next]
    exact sfLayout.scalarFamily_element_member sfFixed sfMixedRaw sfXEntry 33 (by decide)
  have view := sfZFill.view rfl (sfX.element sfFixed account 33) member
  have bank := sfLayout.scalarFamily_bank_agreement sfFixed sfZFill.nextRaw _ member
  rw [sfzfill_next] at view
  exact sfX.read_decoded packedStepFrame sfAliases sfFixed 33 sfMixedRaw (.bool true) rfl bank view

theorem sf_alias_index_read :
    (do
      let loc ← Source.indexLoc (E := sfEnv) packedStepFrame (sfAliases.1.get (.there .here)) 33
      Source.readLoc packedStepFrame loc).run sfAliases = (.ok (.bool true),sfAliases) := by
  rw [Source.Hoare.run_bind,sf_alias_tail_index]
  exact sf_alias_bool_read

theorem sf_alias_out_of_bounds : (Source.indexLoc (E := sfEnv) packedStepFrame (sfAliases.1.get .here) 34).run sfAliases =
    (.error (.revert (Source.panicData .index)),sfAliases) := sfX.indexLoc packedStepFrame sfAliases 34 sf_alias_readLen 34

theorem sf_alias_MemOK : Source.MemOK sfEnv sfState.2.heap.ty sfAliases := by
  have h := sf_mixed_MemOK
  exact ⟨⟨h.1.1,⟨rfl,rfl,trivial⟩⟩,h.2⟩

theorem sf_late_unsupported_keeps_exact_prefix : runScalarOwnership? packedStepFrame sfLayout sfFixed [(0,35)] sfZFill.step.1.2 sfZFill.step.2 =
    (none,sfZFill.step.1.2,sfZFill.step.2) :=
  runScalarOwnership?_unsupported _ _ _ _ _ _ _ _ sf_dirty_growth_fresh_none

end Solidity.Yul.Views.Controls
