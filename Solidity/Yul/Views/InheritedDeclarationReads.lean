import Solidity.Yul.Views.InheritedDeclarationFinal
import Solidity.Yul.Views.InheritedDeclarationNegativeControls

namespace Solidity.Yul.Views.Controls

def diamondItemsReference : Source.Val diamondEnv.layout diamondItemsTy := .storRef rfl (diamondPath "items")
def diamondAliasState : Source.EMState diamondEnv [diamondItemsTy,diamondItemsTy] :=
  ⟨.cons diamondItemsReference (.cons diamondItemsReference .nil),diamondFrame6.1.2.2⟩

theorem diamond_alias_MemOK : Source.MemOK diamondEnv diamondState.2.heap.ty diamondAliasState := by
  have h := diamond_written_MemOK
  exact ⟨⟨h.1.1,⟨rfl,rfl,trivial⟩⟩,h.2⟩

theorem diamond_alias_child_references :
    (do
      let loc ← Source.indexLoc (E := diamondEnv) packedStepFrame (diamondAliasState.1.get .here) 0
      Source.readLoc packedStepFrame loc).run diamondAliasState =
        (.ok (.storRef rfl ⟨diamondName "items",[.index 0]⟩),diamondAliasState) ∧
    (do
      let loc ← Source.indexLoc (E := diamondEnv) packedStepFrame (diamondAliasState.1.get (.there .here)) 1
      Source.readLoc packedStepFrame loc).run diamondAliasState =
        (.ok (.storRef rfl ⟨diamondName "items",[.index 1]⟩),diamondAliasState) := ⟨rfl,rfl⟩

theorem diamond_actual_member_read :
    (Source.readLoc (E := diamondEnv) (Γ := []) packedStepFrame (τ := .int unsigned16) (.stor (diamondItemPath 1 1))).run diamondFrame6.1.2 =
      (.ok (.int 0x2223 (by decide)),diamondFrame6.1.2) := rfl

theorem diamond_actual_index_error :
    (Source.indexLoc (E := diamondEnv) (Γ := []) packedStepFrame diamondItemsReference 2).run diamondFrame6.1.2 =
      (.error (.revert (Source.panicData .index)),diamondFrame6.1.2) := rfl

theorem diamond_actual_declared_transient_read :
    (Source.readLoc (E := diamondEnv) (Γ := []) packedStepFrame (τ := .int unsigned16) (.stor (diamondPath "temp"))).run diamondTempFrame.1.2 =
      (.ok (.int 0x7788 (by decide)),diamondTempFrame.1.2) := rfl

end Solidity.Yul.Views.Controls

namespace Solidity.Yul.Views.Controls

theorem diamond_all_actual_source_readback (c : ScalarPath diamondEnv.layout (diamondEnv.lay account))
    (member : c ∈ diamondChecked.registrations) :
    ∃ v, (Source.readCell (E := diamondEnv) packedStepFrame c.path).run diamondFrame6.1.2 = (.ok v,diamondFrame6.1.2) ∧
      c.codec.encode v = c.field.findWord (diamondSnapshot c.slot) := by
  apply diamondChecked.readCell_view packedStepFrame diamondFrame6.1.2 diamondSnapshot _ c member
  exact finiteEncode_view diamondChecked.registrations _ diamondStore.2 diamondSnapshot diamondChecked.separated diamond_actual_full_reencode

theorem diamond_actual_transient_view : finiteView diamondTempChecked.registrations
    (diamondTempFrame.1.2.2.ex.transient.cells account) (fun _ => diamondTempRaw) := by
  exact (finiteViewBool_iff _ _ _).mp (by decide)

theorem diamond_all_actual_transient_readback (c : ScalarPath diamondEnv.layout (diamondEnv.lay account))
    (member : c ∈ diamondTempChecked.registrations) :
    ∃ v, (Source.readCell (E := diamondEnv) packedStepFrame c.path).run diamondTempFrame.1.2 = (.ok v,diamondTempFrame.1.2) ∧
      c.codec.encode v = c.field.findWord diamondTempRaw :=
  diamondTempChecked.readCell_view packedStepFrame diamondTempFrame.1.2 (fun _ => diamondTempRaw) diamond_actual_transient_view c member

end Solidity.Yul.Views.Controls
