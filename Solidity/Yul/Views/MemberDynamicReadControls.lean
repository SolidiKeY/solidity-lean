import Solidity.Yul.Views.MemberDynamicSequence

namespace Solidity.Yul.Views.Controls

theorem md_x_read (i : Nat) (bound : i < 18) :
    (Source.readLoc (E := mdEnv) packedStepFrame (Source.Loc.stor (τ := .int mdU16) (mdX.elementPath i))).run mdRegrowY.step.1.2 =
      (.ok ((mdX.element_type i) ▸ mdX.elementValue mdFixed account i (mdRegrowYRaw (mdX.element mdFixed account i).slot)),mdRegrowY.step.1.2) := by
  have member : mdX.element mdFixed account i ∈ mdRegrowY.next := by
    change _ ∈ mdLayout.snapshot mdFixed mdRegrowY.nextRaw
    rw [mdRegrowY_next]
    apply mdLayout.snapshot_live_member mdFixed mdRegrowYRaw mdXEntry
    exact (mdX.elements_member mdFixed account _ _).mpr ⟨i,bound,rfl⟩
  have view := mdRegrowY.view rfl (mdX.element mdFixed account i) member
  have bank := mdLayout.snapshot_bank mdFixed mdRegrowY.nextRaw _ member
  rw [mdRegrowY_next] at view
  exact mdX.read_element packedStepFrame mdRegrowY.step.1.2 mdFixed i mdRegrowYRaw bank view

theorem md_y_read (i : Nat) (bound : i < 12) :
    (Source.readLoc (E := mdEnv) packedStepFrame (Source.Loc.stor (τ := .int mdI24) (mdY.elementPath i))).run mdRegrowY.step.1.2 =
      (.ok ((mdY.element_type i) ▸ mdY.elementValue mdFixed account i (mdRegrowYRaw (mdY.element mdFixed account i).slot)),mdRegrowY.step.1.2) := by
  have member : mdY.element mdFixed account i ∈ mdRegrowY.next := by
    change _ ∈ mdLayout.snapshot mdFixed mdRegrowY.nextRaw
    rw [mdRegrowY_next]
    apply mdLayout.snapshot_live_member mdFixed mdRegrowYRaw mdYEntry
    exact (mdY.elements_member mdFixed account _ _).mpr ⟨i,bound,rfl⟩
  have view := mdRegrowY.view rfl (mdY.element mdFixed account i) member
  have bank := mdLayout.snapshot_bank mdFixed mdRegrowY.nextRaw _ member
  rw [mdRegrowY_next] at view
  exact mdY.read_element packedStepFrame mdRegrowY.step.1.2 mdFixed i mdRegrowYRaw bank view

theorem md_unsigned_tail77 :
    (Source.readLoc (E := mdEnv) packedStepFrame (Source.Loc.stor (τ := .int mdU16)
      ⟨mdName "box",[.field 1,.index 16]⟩)).run mdRegrowY.step.1.2 =
      (.ok (.int 77 (by decide)),mdRegrowY.step.1.2) := md_x_read 16 (by decide)

theorem md_signed_minus1 :
    (Source.readLoc (E := mdEnv) packedStepFrame (Source.Loc.stor (τ := .int mdI24)
      ⟨mdName "box",[.field 2,.index 0]⟩)).run mdRegrowY.step.1.2 =
      (.ok (.int (-1) (by decide)),mdRegrowY.step.1.2) := md_y_read 0 (by decide)

def mdArray : Source.STy := .array .storage (.int mdU16) none
def mdAliases : Source.EMState mdEnv [mdArray,mdArray] :=
  ⟨.cons mdX.reference (.cons mdX.reference .nil),mdRegrowY.step.1.2.2⟩

theorem md_alias_length : (Source.readLen (E := mdEnv) packedStepFrame ((mdPath "box").go (.field 1))).run mdAliases = (.ok 18,mdAliases) := by
  have member := mdLayout.snapshot_root_member mdFixed mdRegrowY.nextRaw (mdX.registration account) (mdLayout.header_member mdXEntry)
  have view := mdRegrowY.view rfl (mdX.registration account) member
  have cell := mdX.view_length_cell account _ mdRegrowY.nextRaw view
  have read := mdX.readLen packedStepFrame mdAliases (mdRegrowY.nextRaw 1) rfl cell
  rw [mdRegrowY_next] at read
  exact read

theorem md_alias_value :
    (Source.readLoc (E := mdEnv) packedStepFrame (Source.Loc.stor (τ := .int mdU16)
      ⟨mdName "box",[.field 1,.index 16]⟩)).run mdAliases = (.ok (.int 77 (by decide)),mdAliases) := by
  have member : mdX.element mdFixed account 16 ∈ mdRegrowY.next := by
    change _ ∈ mdLayout.snapshot mdFixed mdRegrowY.nextRaw
    rw [mdRegrowY_next]
    apply mdLayout.snapshot_live_member mdFixed mdRegrowYRaw mdXEntry
    exact (mdX.elements_member mdFixed account _ _).mpr ⟨16,by decide,rfl⟩
  have view := mdRegrowY.view rfl (mdX.element mdFixed account 16) member
  have bank := mdLayout.snapshot_bank mdFixed mdRegrowY.nextRaw _ member
  rw [mdRegrowY_next] at view
  exact mdX.read_element packedStepFrame mdAliases mdFixed 16 mdRegrowYRaw bank view

theorem md_two_actual_aliases :
    (do let loc ← Source.indexLoc (E := mdEnv) packedStepFrame (mdAliases.1.get .here) 16
        Source.readLoc packedStepFrame loc).run mdAliases = (.ok (.int 77 (by decide)),mdAliases) ∧
    (do let loc ← Source.indexLoc (E := mdEnv) packedStepFrame (mdAliases.1.get (.there .here)) 16
        Source.readLoc packedStepFrame loc).run mdAliases = (.ok (.int 77 (by decide)),mdAliases) := by
  have first : (Source.indexLoc (E := mdEnv) packedStepFrame (mdAliases.1.get .here) 16).run mdAliases =
      (.ok (.stor ⟨mdName "box",[.field 1,.index 16]⟩),mdAliases) := mdX.indexLoc packedStepFrame mdAliases 18 md_alias_length 16
  have second : (Source.indexLoc (E := mdEnv) packedStepFrame (mdAliases.1.get (.there .here)) 16).run mdAliases =
      (.ok (.stor ⟨mdName "box",[.field 1,.index 16]⟩),mdAliases) := mdX.indexLoc packedStepFrame mdAliases 18 md_alias_length 16
  constructor
  · rw [Source.Hoare.run_bind,first]; exact md_alias_value
  · rw [Source.Hoare.run_bind,second]; exact md_alias_value

theorem md_alias_bounds : (Source.indexLoc (E := mdEnv) packedStepFrame (mdAliases.1.get .here) 18).run mdAliases =
    (.error (.revert (Source.panicData .index)),mdAliases) := mdX.indexLoc packedStepFrame mdAliases 18 md_alias_length 18

theorem md_alias_MemOK : Source.MemOK mdEnv mdState.2.heap.ty mdAliases := by
  have h := md_written_MemOK
  exact ⟨⟨h.1.1,⟨rfl,rfl,trivial⟩⟩,h.2⟩

end Solidity.Yul.Views.Controls
