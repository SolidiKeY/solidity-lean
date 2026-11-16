import Solidity.Yul.Views.PackedOwnershipBanks
import Solidity.Yul.Views.GenericFlow.Batch

namespace Solidity.Yul.Views

/-- Canonical PREPARATION runner, not Yul execution/admission. None retains the
actual successful prefix's whole source/residual state. A source error stops
with its exact result and state. Finite request length is the recursion index;
there is no extra root/length/domain/fuel cap. -/
def runPackedOwnership? {E ds d active Γ} (F : Source.Fr)
    (layout : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) :
    List (Roadmap.Word × Roadmap.Word) → Source.EMState E Γ → ResidualJournal complementCarrierOwnership →
      (Option (Except Source.Halt Unit) × Source.EMState E Γ × ResidualJournal complementCarrierOwnership)
  | [],s,r => (some (.ok ()),s,r)
  | (q,v)::rest,s,r => match preparePackedOwnership? F layout fixed q v s r with
    | none => (none,s,r)
    | some p => match p.step.1.1 with
      | .error e => (some (.error e),p.step.1.2,p.step.2)
      | .ok () => runPackedOwnership? F layout fixed rest p.step.1.2 p.step.2

-- Preserve the legacy recursion and all compiler-generated equations.
set_option smartUnfolding false in
private theorem runPackedOwnership?_generic {E ds d active Γ} (F : Source.Fr)
    (layout : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (requests : List (Roadmap.Word × Roadmap.Word)) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) :
    runPackedOwnership? F layout fixed requests s r =
      GenericFlow.Batch.run? F (packedOwnershipInterface d active Γ F) layout fixed packedSeparationCheck requests s r :=
  GenericFlow.Batch.eq_run_of_equations F (packedOwnershipInterface d active Γ F) layout fixed packedSeparationCheck
    (runPackedOwnership? F layout fixed) (runPackedOwnership?.eq_1 F layout fixed) (fun q v rest s r => runPackedOwnership?.eq_2 F layout fixed s r q v rest) requests s r

theorem runPackedOwnership?_unsupported {E ds d active Γ} (F : Source.Fr)
    (layout : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (q v) (rest) (s : Source.EMState E Γ) (r)
    (missing : preparePackedOwnership? F layout fixed q v s r = none) :
    runPackedOwnership? F layout fixed ((q,v)::rest) s r = (none,s,r) :=
  (runPackedOwnership?_generic F layout fixed ((q,v)::rest) s r).trans
    (GenericFlow.Batch.unsupported F (packedOwnershipInterface d active Γ F) layout fixed packedSeparationCheck q v rest s r missing)

theorem PackedOwnershipPlan.batch_nonstatic {E ds d active Γ F layout fixed written value s r}
    (p : @PackedOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (rest) (static : F.static = false) :
    runPackedOwnership? F layout fixed ((written,value)::rest) s r =
      runPackedOwnership? F layout fixed rest p.step.1.2 p.step.2 :=
  (runPackedOwnership?_generic F layout fixed ((written,value)::rest) s r).trans
    ((GenericFlow.Batch.nonstatic p rest static).trans (runPackedOwnership?_generic F layout fixed rest p.step.1.2 p.step.2).symm)

theorem PackedOwnershipPlan.batch_static {E ds d active Γ F layout fixed written value s r}
    (p : @PackedOwnershipPlan E ds d active Γ F layout fixed written value s r) (rest)
    (static : F.static = true) :
    runPackedOwnership? F layout fixed ((written,value)::rest) s r = (some (.error (.revert [])),s,r) :=
  (runPackedOwnership?_generic F layout fixed ((written,value)::rest) s r).trans (GenericFlow.Batch.static p rest static)

theorem runPackedOwnership?_MemOK {E ds d active Γ} (F : Source.Fr)
    (layout : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (requests) (s : Source.EMState E Γ) (r) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (runPackedOwnership? F layout fixed requests s r).2.1 :=
  (congrArg (fun result => Source.MemOK E H result.2.1) (runPackedOwnership?_generic F layout fixed requests s r)).mpr
    (GenericFlow.Batch.MemOK F (packedOwnershipInterface d active Γ F) layout fixed packedSeparationCheck requests s r H ok)

theorem PackedOwnershipPlan.batch_late_unsupported {E ds d active Γ F layout fixed written value s r}
    (p : @PackedOwnershipPlan E ds d active Γ F layout fixed written value s r) (q v) (rest)
    (static : F.static = false)
    (missing : preparePackedOwnership? F layout fixed q v p.step.1.2 p.step.2 = none) :
    runPackedOwnership? F layout fixed ((written,value)::(q,v)::rest) s r = (none,p.step.1.2,p.step.2) :=
  (runPackedOwnership?_generic F layout fixed ((written,value)::(q,v)::rest) s r).trans
    (GenericFlow.Batch.late_unsupported p q v rest static missing)

end Solidity.Yul.Views
