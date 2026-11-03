import Solidity.Yul.Views.LayoutOriginFinal

namespace Solidity.Yul.Views.Controls

def originItemsReference : Source.Val originEnv.layout originItemsTy := .storRef rfl (originPath "items")
def originAliasState : Source.EMState originEnv [originItemsTy,originItemsTy] :=
  ⟨.cons originItemsReference (.cons originItemsReference .nil),originFrame6.1.2.2⟩

theorem origin_alias_MemOK : Source.MemOK originEnv originState.2.heap.ty originAliasState := by
  have h := origin_written_MemOK
  exact ⟨⟨h.1.1,⟨rfl,rfl,trivial⟩⟩,h.2⟩

theorem origin_alias_child_references :
    (do
      let loc ← Source.indexLoc (E := originEnv) packedStepFrame (originAliasState.1.get .here) 0
      Source.readLoc packedStepFrame loc).run originAliasState =
        (.ok (.storRef rfl ⟨originName "items",[.index 0]⟩),originAliasState) ∧
    (do
      let loc ← Source.indexLoc (E := originEnv) packedStepFrame (originAliasState.1.get (.there .here)) 1
      Source.readLoc packedStepFrame loc).run originAliasState =
        (.ok (.storRef rfl ⟨originName "items",[.index 1]⟩),originAliasState) := ⟨rfl,rfl⟩

theorem origin_actual_member_read :
    (Source.readLoc (E := originEnv) (Γ := []) packedStepFrame (τ := .int unsigned16) (.stor (originItemPath 1 1))).run originFrame6.1.2 =
      (.ok (.int 0x2223 (by decide)),originFrame6.1.2) := rfl

theorem origin_actual_index_error :
    (Source.indexLoc (E := originEnv) (Γ := []) packedStepFrame originItemsReference 2).run originFrame6.1.2 =
      (.error (.revert (Source.panicData .index)),originFrame6.1.2) := rfl

theorem origin_actual_declared_transient_read :
    (Source.readLoc (E := originEnv) (Γ := []) packedStepFrame (τ := .int unsigned16) (.stor (originPath "temp"))).run originTempFrame.1.2 =
      (.ok (.int 0x7788 (by decide)),originTempFrame.1.2) := rfl

end Solidity.Yul.Views.Controls

namespace Solidity.Yul.Views.Controls

theorem origin_all_actual_source_readback (c : ScalarPath originEnv.layout (originEnv.lay account))
    (member : c ∈ originChecked.registrations) :
    ∃ v, (Source.readCell (E := originEnv) packedStepFrame c.path).run originFrame6.1.2 = (.ok v,originFrame6.1.2) ∧
      c.codec.encode v = c.field.findWord (originSnapshot c.slot) := by
  apply originChecked.readCell_view packedStepFrame originFrame6.1.2 originSnapshot _ c member
  exact finiteEncode_view originChecked.registrations _ originStore.2 originSnapshot originChecked.separated origin_actual_full_reencode

theorem origin_actual_transient_view : finiteView originTempChecked.registrations
    (originTempFrame.1.2.2.ex.transient.cells account) (fun _ => originTempRaw) := by
  exact (finiteViewBool_iff _ _ _).mp (by decide)

theorem origin_all_actual_transient_readback (c : ScalarPath originEnv.layout (originEnv.lay account))
    (member : c ∈ originTempChecked.registrations) :
    ∃ v, (Source.readCell (E := originEnv) packedStepFrame c.path).run originTempFrame.1.2 = (.ok v,originTempFrame.1.2) ∧
      c.codec.encode v = c.field.findWord originTempRaw :=
  originTempChecked.readCell_view packedStepFrame originTempFrame.1.2 (fun _ => originTempRaw) origin_actual_transient_view c member

end Solidity.Yul.Views.Controls
