import Solidity.Yul.Views.RecursiveOwnershipBanks
import Solidity.Yul.Views.GenericFlow.Batch

namespace Solidity.Yul.Views

/-- Canonical PREPARATION runner, not Yul execution/admission. None retains the
actual successful prefix's whole source/residual state. A source error stops
with its exact result and state. Finite request length is the recursion index;
there is no extra root/length/domain/fuel cap. -/
abbrev runRecursiveOwnership? {E ds d active Γ} (F : Source.Fr)
    (layout : @RecursiveComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) :
    List (Roadmap.Word × Roadmap.Word) → Source.EMState E Γ → ResidualJournal complementCarrierOwnership →
      (Option (Except Source.Halt Unit) × Source.EMState E Γ × ResidualJournal complementCarrierOwnership) :=
  GenericFlow.Batch.run? F (recursiveOwnershipInterface d active Γ F) layout fixed packedSeparationCheck

theorem runRecursiveOwnership?_unsupported {E ds d active Γ} (F : Source.Fr)
    (layout : @RecursiveComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (q v) (rest) (s : Source.EMState E Γ) (r)
    (missing : prepareRecursiveOwnership? F layout fixed q v s r = none) :
    runRecursiveOwnership? F layout fixed ((q,v)::rest) s r = (none,s,r) :=
  GenericFlow.Batch.unsupported F (recursiveOwnershipInterface d active Γ F) layout fixed packedSeparationCheck q v rest s r missing

theorem RecursiveOwnershipPlan.batch_nonstatic {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (rest) (static : F.static = false) :
    runRecursiveOwnership? F layout fixed ((written,value)::rest) s r =
      runRecursiveOwnership? F layout fixed rest p.step.1.2 p.step.2 :=
  GenericFlow.Batch.nonstatic p rest static

theorem RecursiveOwnershipPlan.batch_static {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (rest)
    (static : F.static = true) :
    runRecursiveOwnership? F layout fixed ((written,value)::rest) s r = (some (.error (.revert [])),s,r) :=
  GenericFlow.Batch.static p rest static

theorem runRecursiveOwnership?_MemOK {E ds d active Γ} (F : Source.Fr)
    (layout : @RecursiveComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (requests) (s : Source.EMState E Γ) (r) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (runRecursiveOwnership? F layout fixed requests s r).2.1 :=
  GenericFlow.Batch.MemOK F (recursiveOwnershipInterface d active Γ F) layout fixed packedSeparationCheck requests s r H ok

theorem RecursiveOwnershipPlan.batch_late_unsupported {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (q v) (rest)
    (static : F.static = false)
    (missing : prepareRecursiveOwnership? F layout fixed q v p.step.1.2 p.step.2 = none) :
    runRecursiveOwnership? F layout fixed ((written,value)::(q,v)::rest) s r = (none,p.step.1.2,p.step.2) :=
  GenericFlow.Batch.late_unsupported p q v rest static missing

end Solidity.Yul.Views
