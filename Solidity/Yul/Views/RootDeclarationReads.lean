import Solidity.Yul.Views.RootDeclarationFinal

namespace Solidity.Yul.Views.Controls

def rootItemsReference : Source.Val rootEnv.layout rootItemsTy := .storRef rfl (rootPath "items")
def rootAliasState : Source.EMState rootEnv [rootItemsTy,rootItemsTy] :=
  ⟨.cons rootItemsReference (.cons rootItemsReference .nil),rootFrame6.1.2.2⟩

theorem root_alias_MemOK : Source.MemOK rootEnv rootState.2.heap.ty rootAliasState := by
  have h := root_written_MemOK
  exact ⟨⟨h.1.1,⟨rfl,rfl,trivial⟩⟩,h.2⟩

theorem root_alias_child_references :
    (do
      let loc ← Source.indexLoc (E := rootEnv) packedStepFrame (rootAliasState.1.get .here) 0
      Source.readLoc packedStepFrame loc).run rootAliasState =
        (.ok (.storRef rfl ⟨rootName "items",[.index 0]⟩),rootAliasState) ∧
    (do
      let loc ← Source.indexLoc (E := rootEnv) packedStepFrame (rootAliasState.1.get (.there .here)) 1
      Source.readLoc packedStepFrame loc).run rootAliasState =
        (.ok (.storRef rfl ⟨rootName "items",[.index 1]⟩),rootAliasState) := ⟨rfl,rfl⟩

theorem root_actual_member_read :
    (Source.readLoc (E := rootEnv) (Γ := []) packedStepFrame (τ := .int unsigned16) (.stor (rootItemPath 1 1))).run rootFrame6.1.2 =
      (.ok (.int 0x2223 (by decide)),rootFrame6.1.2) := rfl

theorem root_actual_index_error :
    (Source.indexLoc (E := rootEnv) (Γ := []) packedStepFrame rootItemsReference 2).run rootFrame6.1.2 =
      (.error (.revert (Source.panicData .index)),rootFrame6.1.2) := rfl

theorem root_actual_declared_transient_read :
    (Source.readLoc (E := rootEnv) (Γ := []) packedStepFrame (τ := .int unsigned16) (.stor (rootPath "temp"))).run rootTempFrame.1.2 =
      (.ok (.int 0x7788 (by decide)),rootTempFrame.1.2) := rfl

theorem root_exact_duplicate_error : prepareRootDeclarations rootDuplicate none false account 0 = .error .duplicateRoots := rfl

theorem root_exact_order_error : prepareRootDeclarations rootTempDeclarations none false account 0 = .error .metadataOrder := rfl

end Solidity.Yul.Views.Controls
