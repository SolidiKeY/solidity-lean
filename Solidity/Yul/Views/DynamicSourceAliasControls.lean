import Solidity.Yul.Views.DynamicJournalControls

namespace Solidity.Yul.Views.Controls

def dynAliasInitial : Source.EMState dynEnv [dynArray,dynArray] :=
  ⟨.cons dynX.reference (.cons dynX.reference .nil),dynStorageState.2⟩

def dynAliasPrefix := runPackedSource packedStepFrame dynPlans dynAliasInitial dynResidual

theorem dyn_source_prefix_alias_reads :
    (Source.lengthOf (E := dynEnv) packedStepFrame (dynAliasPrefix.1.2.1.get .here)).run dynAliasPrefix.1.2 = (.ok 2,dynAliasPrefix.1.2) ∧
    (do
      let loc ← Source.indexLoc (E := dynEnv) packedStepFrame (dynAliasPrefix.1.2.1.get (.there .here)) 1
      Source.readLoc packedStepFrame loc).run dynAliasPrefix.1.2 =
        (.ok (.int 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff (by decide)),dynAliasPrefix.1.2) := ⟨rfl,rfl⟩

theorem dyn_alias_initial_MemOK : Source.MemOK dynEnv dynStorageState.2.heap.ty dynAliasInitial := by
  have h := dyn_initial_MemOK
  exact ⟨⟨h.1.1,⟨rfl,rfl,trivial⟩⟩,h.2⟩

theorem dyn_alias_every_H (H : Source.HeapTy) (ok : Source.MemOK dynEnv H dynAliasInitial) :
    Source.MemOK dynEnv H dynAliasPrefix.1.2 :=
  runPackedSource_MemOK packedStepFrame dynPlans dynAliasInitial dynResidual H ok

theorem dyn_alias_inhabited_MemOK : Source.MemOK dynEnv dynStorageState.2.heap.ty dynAliasPrefix.1.2 :=
  dyn_alias_every_H _ dyn_alias_initial_MemOK

theorem dyn_complete_transaction_reset :
    (companionEndTx dynChildCore).source.transient = Source.Transient.empty ∧
    (companionEndTx dynChildCore).source.journal = [] ∧
    (companionEndTx dynChildCore).residual.journal = [] := ⟨rfl,rfl,rfl⟩

end Solidity.Yul.Views.Controls
