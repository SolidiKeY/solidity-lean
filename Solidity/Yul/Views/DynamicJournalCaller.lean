import Solidity.Yul.Views.DynamicJournalPrepare

-- Serialize concrete proof elaboration to bound pending computed-state memory.
set_option Elab.async false

namespace Solidity.Yul.Views.Controls
def dynCaller := runPackedSource packedStepFrame dynPlans dynStorageState dynResidual
def dynCallerCore : ResidualCompanion dynEnv.layout dynEnv.lay dynEnv.lay complementCarrierOwnership := ⟨dynCaller.1.2.2.ex,dynCaller.2⟩

theorem dyn_actual_caller_sequence : dynCallerCore = runPackedSlots dynCore dynPlans :=
  runPackedSource_companion packedStepFrame dynPlans dynStorageState dynResidual rfl

theorem dyn_caller_actual_lengths : (Source.readLen (E := dynEnv) packedStepFrame (dynPath "xs")).run dynCaller.1.2 = (.ok 2,dynCaller.1.2) ∧
    (Source.readLen (E := dynEnv) packedStepFrame (dynPath "ys")).run dynCaller.1.2 = (.ok 1,dynCaller.1.2) := ⟨rfl,rfl⟩

theorem dyn_caller_actual_success : dynCaller.1.1 = .ok () ∧ dynCaller.1.2.2.ex.journal.length = 5 ∧ dynCaller.2.journal.length = 5 := ⟨rfl,rfl,rfl⟩

end Solidity.Yul.Views.Controls
