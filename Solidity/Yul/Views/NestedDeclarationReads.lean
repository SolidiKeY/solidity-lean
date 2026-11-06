import Solidity.Yul.Views.NestedDeclarationControls

namespace Solidity.Yul.Views.Controls

def nestedArrayTy : Source.STy := .array .storage (.int unsigned24) (some 12)
def nestedArrayReference : Source.Val declBoundaryEnv.layout nestedArrayTy :=
  .storRef rfl ⟨declBoundaryRoot,[.field 0]⟩

def nestedAliasState : Source.EMState declBoundaryEnv [nestedArrayTy,nestedArrayTy] :=
  ⟨.cons nestedArrayReference (.cons nestedArrayReference .nil),nestedFrame6.1.2.2⟩

theorem nested_source_aliases_MemOK : Source.MemOK declBoundaryEnv nestedDeclState.2.heap.ty nestedAliasState := by
  have written := nested_decl_written_MemOK
  exact ⟨⟨written.1.1,⟨rfl,rfl,trivial⟩⟩,written.2⟩

theorem nested_source_keeps_reference :
    (Source.readLoc (E := declBoundaryEnv) (Γ := []) packedStepFrame (τ := nestedArrayTy)
      (.stor ⟨declBoundaryRoot,[.field 0]⟩)).run nestedFrame6.1.2 =
      (.ok nestedArrayReference,nestedFrame6.1.2) := rfl

theorem nested_source_index_location :
    (Source.indexLoc (E := declBoundaryEnv) (Γ := []) packedStepFrame nestedArrayReference 11).run nestedFrame6.1.2 =
      (.ok (.stor (nestedArrayPath declBoundaryRoot 11)),nestedFrame6.1.2) := rfl

theorem nested_source_index_error :
    (Source.indexLoc (E := declBoundaryEnv) (Γ := []) packedStepFrame nestedArrayReference 12).run nestedFrame6.1.2 =
      (.error (.revert (Source.panicData .index)),nestedFrame6.1.2) := rfl

theorem nested_source_alias_reads :
    (do
      let loc ← Source.indexLoc (E := declBoundaryEnv) packedStepFrame (nestedAliasState.1.get (.here)) 0
      Source.readLoc packedStepFrame loc).run nestedAliasState =
        (.ok (.int 1 (by decide)),nestedAliasState) ∧
    (do
      let loc ← Source.indexLoc (E := declBoundaryEnv) packedStepFrame (nestedAliasState.1.get (.there .here)) 11
      Source.readLoc packedStepFrame loc).run nestedAliasState =
        (.ok (.int 12 (by decide)),nestedAliasState) := ⟨rfl,rfl⟩

end Solidity.Yul.Views.Controls
