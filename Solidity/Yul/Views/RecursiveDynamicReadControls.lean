import Solidity.Yul.Views.RecursiveDynamicSequence

namespace Solidity.Yul.Views.Controls

theorem rc_x_read (i : Nat) (bound : i < 18) :
    (Source.readLoc (E := rcEnv) packedStepFrame (Source.Loc.stor (τ := .int rcU16) (rcX.elementPath i))).run rcRegrowY.step.1.2 =
      (.ok ((rcX.element_type i) ▸ rcX.elementValue rcFixed account i (rcRegrowYRaw (rcX.element rcFixed account i).slot)),rcRegrowY.step.1.2) := by
  have member : rcX.element rcFixed account i ∈ rcRegrowY.next := by
    change _ ∈ rcLayout.snapshot rcFixed rcRegrowY.nextRaw
    rw [rcRegrowY_next]
    apply rcLayout.snapshot_live_member rcFixed rcRegrowYRaw rcXEntry
    exact (rcX.elements_member rcFixed account _ _).mpr ⟨i,bound,rfl⟩
  have view := rcRegrowY.view rfl (rcX.element rcFixed account i) member
  have bank := rcLayout.snapshot_bank rcFixed rcRegrowY.nextRaw _ member
  rw [rcRegrowY_next] at view
  exact rcX.read_element packedStepFrame rcRegrowY.step.1.2 rcFixed i rcRegrowYRaw bank view

theorem rc_y_read (i : Nat) (bound : i < 12) :
    (Source.readLoc (E := rcEnv) packedStepFrame (Source.Loc.stor (τ := .int rcI24) (rcY.elementPath i))).run rcRegrowY.step.1.2 =
      (.ok ((rcY.element_type i) ▸ rcY.elementValue rcFixed account i (rcRegrowYRaw (rcY.element rcFixed account i).slot)),rcRegrowY.step.1.2) := by
  have member : rcY.element rcFixed account i ∈ rcRegrowY.next := by
    change _ ∈ rcLayout.snapshot rcFixed rcRegrowY.nextRaw
    rw [rcRegrowY_next]
    apply rcLayout.snapshot_live_member rcFixed rcRegrowYRaw rcYEntry
    exact (rcY.elements_member rcFixed account _ _).mpr ⟨i,bound,rfl⟩
  have view := rcRegrowY.view rfl (rcY.element rcFixed account i) member
  have bank := rcLayout.snapshot_bank rcFixed rcRegrowY.nextRaw _ member
  rw [rcRegrowY_next] at view
  exact rcY.read_element packedStepFrame rcRegrowY.step.1.2 rcFixed i rcRegrowYRaw bank view

theorem rc_unsigned_tail77 :
    (Source.readLoc (E := rcEnv) packedStepFrame (Source.Loc.stor (τ := .int rcU16)
      ⟨rcName "box",[.field 1,.field 1,.field 0,.index 16]⟩)).run rcRegrowY.step.1.2 =
      (.ok (.int 77 (by decide)),rcRegrowY.step.1.2) := rc_x_read 16 (by decide)

theorem rc_signed_minus1 :
    (Source.readLoc (E := rcEnv) packedStepFrame (Source.Loc.stor (τ := .int rcI24)
      ⟨rcName "box",[.field 1,.field 1,.field 1,.index 0]⟩)).run rcRegrowY.step.1.2 =
      (.ok (.int (-1) (by decide)),rcRegrowY.step.1.2) := rc_y_read 0 (by decide)

def rcArray : Source.STy := .array .storage (.int rcU16) none
def rcAliases : Source.EMState rcEnv [rcArray,rcArray] :=
  ⟨.cons rcX.reference (.cons rcX.reference .nil),rcRegrowY.step.1.2.2⟩

theorem rc_alias_length : (Source.readLen (E := rcEnv) packedStepFrame rcXPath).run rcAliases = (.ok 18,rcAliases) := by
  have member := rcLayout.snapshot_root_member rcFixed rcRegrowY.nextRaw (rcX.registration account) (rcLayout.header_member rcXEntry)
  have view := rcRegrowY.view rfl (rcX.registration account) member
  have cell := rcX.view_length_cell account _ rcRegrowY.nextRaw view
  have read := rcX.readLen packedStepFrame rcAliases (rcRegrowY.nextRaw 2) rfl cell
  rw [rcRegrowY_next] at read
  exact read

theorem rc_alias_value :
    (Source.readLoc (E := rcEnv) packedStepFrame (Source.Loc.stor (τ := .int rcU16)
      ⟨rcName "box",[.field 1,.field 1,.field 0,.index 16]⟩)).run rcAliases = (.ok (.int 77 (by decide)),rcAliases) := by
  have member : rcX.element rcFixed account 16 ∈ rcRegrowY.next := by
    change _ ∈ rcLayout.snapshot rcFixed rcRegrowY.nextRaw
    rw [rcRegrowY_next]
    apply rcLayout.snapshot_live_member rcFixed rcRegrowYRaw rcXEntry
    exact (rcX.elements_member rcFixed account _ _).mpr ⟨16,by decide,rfl⟩
  have view := rcRegrowY.view rfl (rcX.element rcFixed account 16) member
  have bank := rcLayout.snapshot_bank rcFixed rcRegrowY.nextRaw _ member
  rw [rcRegrowY_next] at view
  exact rcX.read_element packedStepFrame rcAliases rcFixed 16 rcRegrowYRaw bank view

theorem rc_two_actual_aliases :
    (do let loc ← Source.indexLoc (E := rcEnv) packedStepFrame (rcAliases.1.get .here) 16
        Source.readLoc packedStepFrame loc).run rcAliases = (.ok (.int 77 (by decide)),rcAliases) ∧
    (do let loc ← Source.indexLoc (E := rcEnv) packedStepFrame (rcAliases.1.get (.there .here)) 16
        Source.readLoc packedStepFrame loc).run rcAliases = (.ok (.int 77 (by decide)),rcAliases) := by
  have first : (Source.indexLoc (E := rcEnv) packedStepFrame (rcAliases.1.get .here) 16).run rcAliases =
      (.ok (.stor ⟨rcName "box",[.field 1,.field 1,.field 0,.index 16]⟩),rcAliases) := rcX.indexLoc packedStepFrame rcAliases 18 rc_alias_length 16
  have second : (Source.indexLoc (E := rcEnv) packedStepFrame (rcAliases.1.get (.there .here)) 16).run rcAliases =
      (.ok (.stor ⟨rcName "box",[.field 1,.field 1,.field 0,.index 16]⟩),rcAliases) := rcX.indexLoc packedStepFrame rcAliases 18 rc_alias_length 16
  constructor
  · rw [Source.Hoare.run_bind,first]; exact rc_alias_value
  · rw [Source.Hoare.run_bind,second]; exact rc_alias_value

theorem rc_alias_bounds : (Source.indexLoc (E := rcEnv) packedStepFrame (rcAliases.1.get .here) 18).run rcAliases =
    (.error (.revert (Source.panicData .index)),rcAliases) := rcX.indexLoc packedStepFrame rcAliases 18 rc_alias_length 18

theorem rc_alias_MemOK : Source.MemOK rcEnv rcState.2.heap.ty rcAliases := by
  have h := rc_written_MemOK
  exact ⟨⟨h.1.1,⟨rfl,rfl,trivial⟩⟩,h.2⟩

end Solidity.Yul.Views.Controls
