import Solidity.Yul.Views.RecursiveOwnershipBanks

namespace Solidity.Yul.Views

/-- Canonical PREPARATION runner, not Yul execution/admission. None retains the
actual successful prefix's whole source/residual state. A source error stops
with its exact result and state. Finite request length is the recursion index;
there is no extra root/length/domain/fuel cap. -/
def runRecursiveOwnership? {E ds d active Γ} (F : Source.Fr)
    (layout : @RecursiveComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) :
    List (Roadmap.Word × Roadmap.Word) → Source.EMState E Γ → ResidualJournal complementCarrierOwnership →
      (Option (Except Source.Halt Unit) × Source.EMState E Γ × ResidualJournal complementCarrierOwnership)
  | [],s,r => (some (.ok ()),s,r)
  | (q,v)::rest,s,r => match prepareRecursiveOwnership? F layout fixed q v s r with
    | none => (none,s,r)
    | some p => match p.step.1.1 with
      | .error e => (some (.error e),p.step.1.2,p.step.2)
      | .ok () => runRecursiveOwnership? F layout fixed rest p.step.1.2 p.step.2

theorem runRecursiveOwnership?_unsupported {E ds d active Γ} (F : Source.Fr)
    (layout : @RecursiveComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (q v) (rest) (s : Source.EMState E Γ) (r)
    (missing : prepareRecursiveOwnership? F layout fixed q v s r = none) :
    runRecursiveOwnership? F layout fixed ((q,v)::rest) s r = (none,s,r) := by
  rw [runRecursiveOwnership?,missing]

theorem RecursiveOwnershipPlan.batch_nonstatic {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (rest) (static : F.static = false) :
    runRecursiveOwnership? F layout fixed ((written,value)::rest) s r =
      runRecursiveOwnership? F layout fixed rest p.step.1.2 p.step.2 := by
  rw [runRecursiveOwnership?,p.prepare_eq]
  have success : p.step.1.1 = .ok () := congrArg (fun z => z.1.1) (p.nonstatic static)
  dsimp only
  rw [success]

theorem RecursiveOwnershipPlan.batch_static {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (rest)
    (static : F.static = true) :
    runRecursiveOwnership? F layout fixed ((written,value)::rest) s r = (some (.error (.revert [])),s,r) := by
  rw [runRecursiveOwnership?,p.prepare_eq]
  dsimp only
  rw [p.static static]

theorem runRecursiveOwnership?_MemOK {E ds d active Γ} (F : Source.Fr)
    (layout : @RecursiveComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (requests) (s : Source.EMState E Γ) (r) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (runRecursiveOwnership? F layout fixed requests s r).2.1 := by
  induction requests generalizing s r with
  | nil => exact ok
  | cons request rest ih =>
    obtain ⟨q,v⟩ := request
    unfold runRecursiveOwnership?
    split
    next absent => exact ok
    next p prepared =>
      split
      next error failed => exact p.MemOK H ok
      next success => exact ih p.step.1.2 p.step.2 (p.MemOK H ok)

theorem RecursiveOwnershipPlan.batch_late_unsupported {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (q v) (rest)
    (static : F.static = false)
    (missing : prepareRecursiveOwnership? F layout fixed q v p.step.1.2 p.step.2 = none) :
    runRecursiveOwnership? F layout fixed ((written,value)::(q,v)::rest) s r = (none,p.step.1.2,p.step.2) := by
  rw [p.batch_nonstatic _ static]
  exact runRecursiveOwnership?_unsupported F layout fixed q v rest p.step.1.2 p.step.2 missing

end Solidity.Yul.Views
