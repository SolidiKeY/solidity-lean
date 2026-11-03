import Solidity.Yul.Views.FixedDeclarationJournal

namespace Solidity.Yul.Views.Controls

def recursiveArrayTy : Source.STy := .array .storage (.int recursiveUnsigned128) (some 3)
def recursiveArrayReference : Source.Val recursiveDeclEnv.layout recursiveArrayTy :=
  .storRef rfl ⟨recursiveRoot,[.field 1]⟩

def recursiveAliasState : Source.EMState recursiveDeclEnv [recursiveArrayTy,recursiveArrayTy] :=
  ⟨.cons recursiveArrayReference (.cons recursiveArrayReference .nil),recursiveFrame13.1.2.2⟩

theorem recursive_source_aliases_MemOK : Source.MemOK recursiveDeclEnv recursiveState.2.heap.ty recursiveAliasState := by
  have written := recursive_written_MemOK
  exact ⟨⟨written.1.1,⟨rfl,rfl,trivial⟩⟩,written.2⟩

theorem recursive_source_keeps_reference :
    (Source.readLoc (E := recursiveDeclEnv) (Γ := []) packedStepFrame (τ := recursiveArrayTy)
      (.stor ⟨recursiveRoot,[.field 1]⟩)).run recursiveFrame13.1.2 =
      (.ok recursiveArrayReference,recursiveFrame13.1.2) := rfl

theorem recursive_source_index_location :
    (Source.indexLoc (E := recursiveDeclEnv) (Γ := []) packedStepFrame recursiveArrayReference 2).run recursiveFrame13.1.2 =
      (.ok (.stor (recursiveValuePath 2)),recursiveFrame13.1.2) := rfl

theorem recursive_source_index_error :
    (Source.indexLoc (E := recursiveDeclEnv) (Γ := []) packedStepFrame recursiveArrayReference 3).run recursiveFrame13.1.2 =
      (.error (.revert (Source.panicData .index)),recursiveFrame13.1.2) := rfl

theorem recursive_source_alias_reads :
    (do
      let loc ← Source.indexLoc (E := recursiveDeclEnv) packedStepFrame (recursiveAliasState.1.get (.here)) 0
      Source.readLoc packedStepFrame loc).run recursiveAliasState =
        (.ok (.int 1 (by decide)),recursiveAliasState) ∧
    (do
      let loc ← Source.indexLoc (E := recursiveDeclEnv) packedStepFrame (recursiveAliasState.1.get (.there .here)) 2
      Source.readLoc packedStepFrame loc).run recursiveAliasState =
        (.ok (.int 3 (by decide)),recursiveAliasState) := ⟨rfl,rfl⟩

end Solidity.Yul.Views.Controls
