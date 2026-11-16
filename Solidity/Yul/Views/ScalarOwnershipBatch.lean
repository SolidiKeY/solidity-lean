import Solidity.Yul.Views.ScalarOwnershipBanks
import Solidity.Yul.Views.GenericFlow.Batch

namespace Solidity.Yul.Views

/-- Canonical PREPARATION runner, not Yul execution/admission. None retains the
actual successful prefix's whole source/residual state. A source error stops
with its exact result and state. Finite request length is the recursion index;
there is no extra root/length/domain/fuel cap. -/
def runScalarOwnership? {E ds d active Γ} (F : Source.Fr)
    (layout : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) :
    List (Roadmap.Word × Roadmap.Word) → Source.EMState E Γ → ResidualJournal complementCarrierOwnership →
      (Option (Except Source.Halt Unit) × Source.EMState E Γ × ResidualJournal complementCarrierOwnership)
  | [],s,r => (some (.ok ()),s,r)
  | (q,v)::rest,s,r => match prepareScalarOwnership? F layout fixed q v s r with
    | none => (none,s,r)
    | some p => match p.step.1.1 with
      | .error e => (some (.error e),p.step.1.2,p.step.2)
      | .ok () => runScalarOwnership? F layout fixed rest p.step.1.2 p.step.2

-- Preserve the legacy recursion and all compiler-generated equations.
set_option smartUnfolding false in
private theorem runScalarOwnership?_generic {E ds d active Γ} (F : Source.Fr)
    (layout : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (requests : List (Roadmap.Word × Roadmap.Word)) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) :
    runScalarOwnership? F layout fixed requests s r =
      GenericFlow.Batch.run? F (scalarOwnershipInterface d active Γ F) layout fixed packedSeparationCheck requests s r :=
  GenericFlow.Batch.eq_run_of_equations F (scalarOwnershipInterface d active Γ F) layout fixed packedSeparationCheck
    (runScalarOwnership? F layout fixed) (runScalarOwnership?.eq_1 F layout fixed) (fun q v rest s r => runScalarOwnership?.eq_2 F layout fixed s r q v rest) requests s r

theorem runScalarOwnership?_unsupported {E ds d active Γ} (F : Source.Fr)
    (layout : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (q v) (rest) (s : Source.EMState E Γ) (r)
    (missing : prepareScalarOwnership? F layout fixed q v s r = none) :
    runScalarOwnership? F layout fixed ((q,v)::rest) s r = (none,s,r) :=
  (runScalarOwnership?_generic F layout fixed ((q,v)::rest) s r).trans
    (GenericFlow.Batch.unsupported F (scalarOwnershipInterface d active Γ F) layout fixed packedSeparationCheck q v rest s r missing)

theorem ScalarOwnershipPlan.batch_nonstatic {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (rest) (static : F.static = false) :
    runScalarOwnership? F layout fixed ((written,value)::rest) s r =
      runScalarOwnership? F layout fixed rest p.step.1.2 p.step.2 :=
  (runScalarOwnership?_generic F layout fixed ((written,value)::rest) s r).trans
    ((GenericFlow.Batch.nonstatic p rest static).trans (runScalarOwnership?_generic F layout fixed rest p.step.1.2 p.step.2).symm)

theorem ScalarOwnershipPlan.batch_static {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (rest)
    (static : F.static = true) :
    runScalarOwnership? F layout fixed ((written,value)::rest) s r = (some (.error (.revert [])),s,r) :=
  (runScalarOwnership?_generic F layout fixed ((written,value)::rest) s r).trans (GenericFlow.Batch.static p rest static)

theorem runScalarOwnership?_MemOK {E ds d active Γ} (F : Source.Fr)
    (layout : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (requests) (s : Source.EMState E Γ) (r) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (runScalarOwnership? F layout fixed requests s r).2.1 :=
  (congrArg (fun result => Source.MemOK E H result.2.1) (runScalarOwnership?_generic F layout fixed requests s r)).mpr
    (GenericFlow.Batch.MemOK F (scalarOwnershipInterface d active Γ F) layout fixed packedSeparationCheck requests s r H ok)

theorem ScalarOwnershipPlan.batch_late_unsupported {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (q v) (rest)
    (static : F.static = false)
    (missing : prepareScalarOwnership? F layout fixed q v p.step.1.2 p.step.2 = none) :
    runScalarOwnership? F layout fixed ((written,value)::(q,v)::rest) s r = (none,p.step.1.2,p.step.2) :=
  (runScalarOwnership?_generic F layout fixed ((written,value)::(q,v)::rest) s r).trans
    (GenericFlow.Batch.late_unsupported p q v rest static missing)

end Solidity.Yul.Views
