import Solidity.Yul.Views.ScalarOwnershipBanks

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

theorem runScalarOwnership?_unsupported {E ds d active Γ} (F : Source.Fr)
    (layout : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (q v) (rest) (s : Source.EMState E Γ) (r)
    (missing : prepareScalarOwnership? F layout fixed q v s r = none) :
    runScalarOwnership? F layout fixed ((q,v)::rest) s r = (none,s,r) := by
  rw [runScalarOwnership?,missing]

theorem ScalarOwnershipPlan.batch_nonstatic {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (rest) (static : F.static = false) :
    runScalarOwnership? F layout fixed ((written,value)::rest) s r =
      runScalarOwnership? F layout fixed rest p.step.1.2 p.step.2 := by
  rw [runScalarOwnership?,p.prepare_eq]
  have success : p.step.1.1 = .ok () := congrArg (fun z => z.1.1) (p.nonstatic static)
  dsimp only
  rw [success]

theorem ScalarOwnershipPlan.batch_static {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (rest)
    (static : F.static = true) :
    runScalarOwnership? F layout fixed ((written,value)::rest) s r = (some (.error (.revert [])),s,r) := by
  rw [runScalarOwnership?,p.prepare_eq]
  dsimp only
  rw [p.static static]

theorem runScalarOwnership?_MemOK {E ds d active Γ} (F : Source.Fr)
    (layout : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (requests) (s : Source.EMState E Γ) (r) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (runScalarOwnership? F layout fixed requests s r).2.1 := by
  induction requests generalizing s r with
  | nil => exact ok
  | cons request rest ih =>
    obtain ⟨q,v⟩ := request
    unfold runScalarOwnership?
    split
    next absent => exact ok
    next p prepared =>
      split
      next error failed => exact p.MemOK H ok
      next success => exact ih p.step.1.2 p.step.2 (p.MemOK H ok)

theorem ScalarOwnershipPlan.batch_late_unsupported {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (q v) (rest)
    (static : F.static = false)
    (missing : prepareScalarOwnership? F layout fixed q v p.step.1.2 p.step.2 = none) :
    runScalarOwnership? F layout fixed ((written,value)::(q,v)::rest) s r = (none,p.step.1.2,p.step.2) := by
  rw [p.batch_nonstatic _ static]
  exact runScalarOwnership?_unsupported F layout fixed q v rest p.step.1.2 p.step.2 missing

end Solidity.Yul.Views
